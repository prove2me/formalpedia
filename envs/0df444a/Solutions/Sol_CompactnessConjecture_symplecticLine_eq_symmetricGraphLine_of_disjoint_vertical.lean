-- Prove2me | solution 1 for CompactnessConjecture.symplecticLine_eq_symmetricGraphLine_of_disjoint_vertical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/a7846385-95d2-4424-9a55-1faa0053cd0d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticLineGraphMap_graphVector

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    ∃ a b c : K, L = symmetricGraphLine K a b c := by
  let a := symplecticLineGraphMap K L hvertical ![1, 0] 0
  let b := symplecticLineGraphMap K L hvertical ![0, 1] 0
  let c := symplecticLineGraphMap K L hvertical ![0, 1] 1
  refine ⟨a, b, c, ?_⟩
  apply Subtype.ext
  change L.1 = LinearMap.range (symmetricGraphLinearMap K a b c)
  apply le_antisymm
  · intro w hw
    let x : L.1 := ⟨w, hw⟩
    let z := symplecticHorizontalProjection K
      (w : SymplecticVector K)
    refine ⟨z, ?_⟩
    change symmetricGraphVector K a b c (z 0) (z 1) = w
    have hgraph := symplecticLineGraphMap_graphVector
      K L hvertical z
    have hpreimage :
        (symplecticLineHorizontalProjectionEquiv K L hvertical).symm z =
          x := by
      apply
        (symplecticLineHorizontalProjectionEquiv K L hvertical).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    change
      symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) = w
    rw [hgraph, hpreimage]
  · intro w hw
    obtain ⟨z, rfl⟩ := hw
    change
      symmetricGraphVector K a b c (z 0) (z 1) ∈ L.1
    change
      symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) ∈ L.1
    rw [symplecticLineGraphMap_graphVector K L hvertical z]
    exact ((symplecticLineHorizontalProjectionEquiv
      K L hvertical).symm z).2
end CompactnessConjecture
