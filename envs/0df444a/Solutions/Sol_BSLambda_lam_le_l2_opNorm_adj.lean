-- Prove2me | solution 1 for BSLambda.lam_le_l2_opNorm_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:58:32.842469+00:00
-- url     : https://prove2.me/submissions/dc199733-4b8c-4fc1-b594-d28bb678452c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Theorems.Thm_Matrix_IsHermitian_ciSup_eigenvalues_le_l2_opNorm


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) : lam f ≤ ‖adj f‖ :=
  (isHermitian_adj f).ciSup_eigenvalues_le_l2_opNorm
end BSLambda
