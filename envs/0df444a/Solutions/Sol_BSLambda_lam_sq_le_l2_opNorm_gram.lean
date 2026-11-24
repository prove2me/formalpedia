-- Prove2me | solution 1 for BSLambda.lam_sq_le_l2_opNorm_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:38.487385+00:00
-- url     : https://prove2.me/submissions/aa686411-e380-4076-814b-fcd6653ab5e7

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Theorems.Thm_BSLambda_l2_opNorm_adj_le
public import Theorems.Thm_BSLambda_l2_opNorm_gram
public import Theorems.Thm_BSLambda_lam_le_l2_opNorm_adj
public import Theorems.Thm_BSLambda_lam_nonneg


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) : lam f ^ 2 ≤ ‖gram f‖ := by
  rw [l2_opNorm_gram, ← sq]
  calc lam f ^ 2 ≤ ‖adj f‖ ^ 2 := pow_le_pow_left₀ (lam_nonneg f) (lam_le_l2_opNorm_adj f) 2
    _ ≤ ‖biadj f‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_adj_le f) 2
end BSLambda
