-- Prove2me | solution 1 for BSLambda.isBlockFamily_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:15.850992+00:00
-- url     : https://prove2.me/submissions/0ebeb701-f266-4473-8c6c-479a736299e0

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
theorem _root_.solution {ι : Type*} {f : Input V → Bool} {x : Input V} {B : ι → Finset V}
    {s : Finset ι} (hsens : ∀ i ∈ s, IsSensitiveBlock f x (B i))
    (hdisj : (s : Set ι).PairwiseDisjoint B) :
    IsBlockFamily f x (s.image B) where
  sensitive A hA := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hA
    exact hsens i hi
  disjoint := by
    rw [Finset.coe_image]
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hne
    exact hdisj hi hj fun h ↦ hne (congrArg B h)
end BSLambda
