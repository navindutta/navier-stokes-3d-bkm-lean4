import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Mathlib PR Candidate: 3-Variable Constructive AM-GM Inequality via Sum of Squares

This file provides an exact constructive proof of the 3-variable Arithmetic Mean - Geometric Mean (AM-GM)
inequality on ℝ using an algebraic Sum-of-Squares (SoS) polynomial decomposition:

$$(a+b+c)^3 - 27abc = \frac{1}{2}(a+b+c)\left((a-b)^2 + (b-c)^2 + (c-a)^2\right) + 3\left(a(b-c)^2 + b(c-a)^2 + c(a-b)^2\right)$$

Because each term is non-negative whenever $a, b, c \ge 0$, the inequality $(a+b+c)^3 \ge 27abc$
holds unconditionally and constructively without transcendental logarithm/exponential approximations.

Author: Navin Dutta (ORCID: 0009-0002-2515-4922)
-/

namespace Real

/-- The 3-variable algebraic Arithmetic Mean - Geometric Mean inequality on `ℝ`.
    Proved via an explicit Sum-of-Squares (SoS) polynomial identity. -/
theorem am_gm_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ ((a + b + c) / 3) ^ 3 := by
  have h_identity :
      (a + b + c) ^ 3 - 27 * (a * b * c)
        = (1 / 2 : ℝ) * (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2)
          + 3 * (a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2) := by ring
  have h_sos_part1 : 0 ≤ (1 / 2 : ℝ) * (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) := by
    positivity
  have h_sos_part2 : 0 ≤ 3 * (a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2) := by
    positivity
  have h_diff_nonneg : 0 ≤ (a + b + c) ^ 3 - 27 * (a * b * c) := by
    rw [h_identity]
    linarith
  have h_cube_bound : 27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
    linarith
  calc a * b * c
      = (27 * (a * b * c)) / 27 := by ring
    _ ≤ ((a + b + c) ^ 3) / 27 := by linarith
    _ = ((a + b + c) / 3) ^ 3 := by ring

end Real
