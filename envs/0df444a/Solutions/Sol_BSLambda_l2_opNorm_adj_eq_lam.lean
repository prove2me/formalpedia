-- Prove2me | solution 1 for BSLambda.l2_opNorm_adj_eq_lam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:05.535815+00:00
-- url     : https://prove2.me/submissions/0563dbd9-7c92-453d-8d72-7950848bbdaf

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Theorems.Thm_BSLambda_l2_opNorm_adj_le_lam
public import Theorems.Thm_BSLambda_lam_le_l2_opNorm_adj


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) : ‖adj f‖ = lam f :=
  le_antisymm (l2_opNorm_adj_le_lam f) (lam_le_l2_opNorm_adj f)
end BSLambda
