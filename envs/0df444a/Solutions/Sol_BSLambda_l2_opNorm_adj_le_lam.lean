-- Prove2me | solution 1 for BSLambda.l2_opNorm_adj_le_lam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:19.500643+00:00
-- url     : https://prove2.me/submissions/2baa82d5-6ea4-444d-976e-c6025b312288

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Theorems.Thm_BSLambda_abs_eigenvalues_adj_le_lam
public import Theorems.Thm_Matrix_IsHermitian_l2_opNorm_le_of_abs_eigenvalues_le


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) : ‖adj f‖ ≤ lam f :=
  (isHermitian_adj f).l2_opNorm_le_of_abs_eigenvalues_le (abs_eigenvalues_adj_le_lam f)
end BSLambda
