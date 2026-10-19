-- Prove2me | solution 1 for CompactnessConjecture.symmetricGraphLines_disjoint_of_difference_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/38f73c21-6776-46ce-81b8-4a4146dcaf8a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {a b c a' b' c' : K}
    (hdet : symmetricDet (a - a') (b - b') (c - c') ≠ 0) :
    Disjoint (symmetricGraphLine K a b c).1
      (symmetricGraphLine K a' b' c').1 := by
  apply Submodule.disjoint_def.mpr
  intro w hw hw'
  obtain ⟨u, hu⟩ := hw
  obtain ⟨v, hv⟩ := hw'
  have hvector :
      symmetricGraphVector K a b c (u 0) (u 1) =
        symmetricGraphVector K a' b' c' (v 0) (v 1) := by
    exact hu.trans hv.symm
  have hzero := congrFun hvector 0
  have htwo := congrFun hvector 2
  simp [symmetricGraphVector] at hzero htwo
  have huv : u = v := by
    funext i
    fin_cases i
    · exact hzero
    · exact htwo
  subst v
  have hone := congrFun hvector 1
  have hthree := congrFun hvector 3
  simp [symmetricGraphVector] at hone hthree
  have hdetx :
      symmetricDet (a - a') (b - b') (c - c') * u 0 = 0 := by
    unfold symmetricDet
    linear_combination (c - c') * hone - (b - b') * hthree
  have hdety :
      symmetricDet (a - a') (b - b') (c - c') * u 1 = 0 := by
    unfold symmetricDet
    linear_combination -(b - b') * hone + (a - a') * hthree
  have hx : u 0 = 0 :=
    (mul_eq_zero.mp hdetx).resolve_left hdet
  have hy : u 1 = 0 :=
    (mul_eq_zero.mp hdety).resolve_left hdet
  rw [← hu]
  change symmetricGraphVector K a b c (u 0) (u 1) = 0
  funext i
  fin_cases i <;> simp [symmetricGraphVector, hx, hy]
end CompactnessConjecture
