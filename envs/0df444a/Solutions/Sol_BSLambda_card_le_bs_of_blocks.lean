-- Prove2me | solution 1 for BSLambda.card_le_bs_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:34.667344+00:00
-- url     : https://prove2.me/submissions/e669cf32-976c-46fd-86bf-19f3b31913a7

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Theorems.Thm_Set_PairwiseDisjoint_injOn
public import Theorems.Thm_BSLambda_le_bs_of_family
public import Theorems.Thm_BSLambda_isBlockFamily_image

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution {ι : Type*} {f : Input V → Bool} {x : Input V} {B : ι → Finset V}
    {s : Finset ι} (hsens : ∀ i ∈ s, IsSensitiveBlock f x (B i))
    (hdisj : (s : Set ι).PairwiseDisjoint B) : s.card ≤ bs f := by
  rw [← Finset.card_image_of_injOn
    (hdisj.injOn fun i hi ↦ Finset.nonempty_iff_ne_empty.1 (hsens i hi).nonempty)]
  exact le_bs_of_family (isBlockFamily_image hsens hdisj)
end BSLambda
