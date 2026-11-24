-- Prove2me | solution 1 for BSLambda.Final.bs_iter_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:35.970307+00:00
-- url     : https://prove2.me/submissions/720ab1de-808d-41c5-ab80-65025ea114cf

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_card_idx
public import Theorems.Thm_BSLambda_Construction_block_disjoint
public import Theorems.Thm_BSLambda_Construction_block_nonempty
public import Theorems.Thm_BSLambda_Construction_ind_flipSet_block
public import Theorems.Thm_BSLambda_Construction_ind_zeroInput
public import Theorems.Thm_BSLambda_card_pow_le_bs_iterFun


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution (m : ℕ) : 14011 ^ m ≤ bs (iterFun (ind Arc γ) m) := by
  have hr : NeZero r := NeZero.of_pos (by norm_num : (0 : ℕ) < r)
  have h := card_pow_le_bs_iterFun (ind_zeroInput Arc γ) (ind_flipSet_block (Arc := Arc) (γ := γ))
    (block_nonempty (ι := Idx) (r := r)) (fun _ _ hij ↦ block_disjoint hij) m
  rwa [card_idx] at h
end BSLambda.Final
