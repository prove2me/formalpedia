-- Prove2me | solution 1 for CompactnessConjecture.symplecticVertical_mem_coordinateCenter_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/55ef5278-a239-429f-8cba-5f04d7db0f45

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {x y : K} (hxy : x ≠ 0 ∨ y ≠ 0)
    {v : SymplecticVector K}
    (hv : v ∈ (symplecticVerticalLine K).1)
    (horth : standardSymplecticForm K
      (symplecticHorizontalVector K x y) v = 0) :
    v ∈ (coordinateCenterLine K x y hxy).1 := by
  change v ∈ LinearMap.range (symplecticVerticalLinearMap K) at hv
  obtain ⟨z, hz⟩ := hv
  have hv0 : v 0 = 0 := by
    simpa [symplecticVerticalLinearMap] using
      (congrFun hz 0).symm
  have hv2 : v 2 = 0 := by
    simpa [symplecticVerticalLinearMap] using
      (congrFun hz 2).symm
  have heq : x * v 1 + y * v 3 = 0 := by
    simpa [standardSymplecticForm,
      symplecticHorizontalVector] using horth
  change v ∈ LinearMap.range (coordinateCenterLinearMap K x y)
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      rcases hxy with h | h
      · exact False.elim (h hx)
      · exact h
    refine ⟨![0, -(v 1 / y)], ?_⟩
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hv0, hv2] <;>
      field_simp [hy]
    linear_combination -heq
  · refine ⟨![0, v 3 / x], ?_⟩
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hv0, hv2] <;>
      field_simp [hx]
    linear_combination -heq
end CompactnessConjecture
