import Lake
open Lake DSL

package «navier-stokes-3d-bkm-lean4» where
  name := `NS3D

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

lean_lib NS3DGagliardoNirenberg where
  roots := #[`NS3D_GagliardoNirenberg]

lean_lib NS3DBKMCriterion where
  roots := #[`NS3D_BKM_Criterion]

lean_lib NS3DCKNPartialRegularity where
  roots := #[`NS3D_CKN_PartialRegularity]
