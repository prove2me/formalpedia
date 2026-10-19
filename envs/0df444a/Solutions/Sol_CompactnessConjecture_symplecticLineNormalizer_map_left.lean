-- Prove2me | solution 1 for CompactnessConjecture.symplecticLineNormalizer_map_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/1a7e5fae-fe34-40fe-8f49-eb179ed887e5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticLineNormalizer_apply_left

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) L =
      symmetricGraphLine K 0 0 0 := by
  apply Subtype.ext
  change
    L.1.map (symplecticLineNormalizer K L M hLM).toLinearEquiv.toLinearMap =
      LinearMap.range (symmetricGraphLinearMap K 0 0 0)
  apply le_antisymm
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨(symplecticLineBasis K L).equivFun ⟨x, hx⟩, ?_⟩
    simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      (symplecticLineNormalizer_apply_left K L M hLM
        (⟨x, hx⟩ : L.1)).symm
  · intro v hv
    obtain ⟨z, rfl⟩ := hv
    let x : L.1 := (symplecticLineBasis K L).equivFun.symm z
    refine Submodule.mem_map.mpr
      ⟨(x : SymplecticVector K), x.2, ?_⟩
    simpa [x, symmetricGraphLinearMap, symmetricGraphVector] using
      symplecticLineNormalizer_apply_left K L M hLM x
end CompactnessConjecture
