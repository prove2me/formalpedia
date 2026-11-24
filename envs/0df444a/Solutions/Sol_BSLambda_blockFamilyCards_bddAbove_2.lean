-- Prove2me | solution 2 for BSLambda.blockFamilyCards_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:10.409337+00:00
-- url     : https://prove2.me/submissions/ca64a577-4c65-44c1-a530-74eca7e055c1

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BSLambda
theorem _root_.solution [Finite V] (f : Input V → Bool) (x : Input V) :
    BddAbove (blockFamilyCards f x) := by
  let := Fintype.ofFinite V
  refine ⟨Fintype.card (Finset V), ?_⟩
  rintro n ⟨𝓑, -, rfl⟩
  exact Finset.card_le_univ 𝓑
end BSLambda
