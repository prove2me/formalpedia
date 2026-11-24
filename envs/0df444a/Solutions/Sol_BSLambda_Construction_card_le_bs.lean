-- Prove2me | solution 1 for BSLambda.Construction.card_le_bs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:15.130802+00:00
-- url     : https://prove2.me/submissions/384bd8a5-2ef5-4b42-8c94-44280790785d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Theorems.Thm_BSLambda_Construction_isSensitiveBlock_block
public import Theorems.Thm_BSLambda_Construction_block_disjoint
public import Theorems.Thm_BSLambda_card_le_bs_of_blocks


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}
namespace BSLambda.Construction
theorem _root_.solution [Fintype ι] [DecidableEq ι] [NeZero r] :
    Fintype.card ι ≤ bs (ind Arc γ) := by
  rw [← Finset.card_univ (α := ι)]
  exact card_le_bs_of_blocks (fun i _ ↦ isSensitiveBlock_block i)
    fun _ _ _ _ hij ↦ block_disjoint hij
end BSLambda.Construction
