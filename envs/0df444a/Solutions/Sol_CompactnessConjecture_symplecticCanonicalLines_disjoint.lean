-- Prove2me | solution 1 for CompactnessConjecture.symplecticCanonicalLines_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/dded0620-83b3-400e-9c74-af2903f805e2

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution :
    Disjoint (symmetricGraphLine K 0 0 0).1
      (symplecticVerticalLine K).1 := by
  apply Submodule.disjoint_def.mpr
  intro w hwH hwV
  change w ∈ LinearMap.range
    (symmetricGraphLinearMap K 0 0 0) at hwH
  change w ∈ LinearMap.range
    (symplecticVerticalLinearMap K) at hwV
  obtain ⟨z, hz⟩ := hwH
  obtain ⟨t, ht⟩ := hwV
  have heq := hz.trans ht.symm
  have hz0 : z 0 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector,
      symplecticVerticalLinearMap] using congrFun heq 0
  have hz1 : z 1 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector,
      symplecticVerticalLinearMap] using congrFun heq 2
  rw [← hz]
  funext i
  fin_cases i <;>
    simp [symmetricGraphLinearMap, symmetricGraphVector,
      hz0, hz1]
end CompactnessConjecture
