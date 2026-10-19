-- Prove2me | solution 1 for CompactnessConjecture.symmetricGraphLine_coordinateCenter_intersection_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/770d20b7-13f0-4a9c-8e2e-3693149a4fcd

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symmetricQuadratic_eq_bilinear
import Theorems.Thm_CompactnessConjecture_symmetricGraphVector_mem_center_span_iff

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ w : SymplecticVector K,
      w ≠ 0 ∧ w ∈ (symmetricGraphLine K a b c).1 ∧
        w ∈ (coordinateCenterLine K x y hxy).1) ↔
      symmetricQuadratic a b c x y = 0 := by
  constructor
  · rintro ⟨w, hw, hgraph, hcenter⟩
    obtain ⟨u, hu⟩ := hgraph
    obtain ⟨d, hd⟩ := hcenter
    have hvector :
        symmetricGraphVector K a b c (u 0) (u 1) =
          d 0 • symplecticHorizontalVector K x y +
            d 1 • symplecticAnnihilatorVector K x y := by
      exact hu.trans hd.symm
    have hzero := congrFun hvector 0
    have hone := congrFun hvector 1
    have htwo := congrFun hvector 2
    have hthree := congrFun hvector 3
    simp [symmetricGraphVector, symplecticHorizontalVector,
      symplecticAnnihilatorVector, Pi.add_apply,
      smul_eq_mul] at hzero hone htwo hthree
    have hdnonzero : d 0 ≠ 0 := by
      intro hd0
      have hu0 : u 0 = 0 := by
        simpa [hd0] using hzero
      have hu1 : u 1 = 0 := by
        simpa [hd0] using htwo
      apply hw
      rw [← hu]
      change symmetricGraphVector K a b c (u 0) (u 1) = 0
      funext i
      fin_cases i <;> simp [symmetricGraphVector, hu0, hu1]
    have hproduct : d 0 * symmetricQuadratic a b c x y = 0 := by
      rw [symmetricQuadratic_eq_bilinear]
      linear_combination x * hone + y * hthree -
        (a * x + b * y) * hzero -
        (b * x + c * y) * htwo
    exact (mul_eq_zero.mp hproduct).resolve_left hdnonzero
  · intro hquadratic
    obtain ⟨s, t, hvector⟩ :=
      (symmetricGraphVector_mem_center_span_iff K hxy).mpr hquadratic
    refine ⟨symmetricGraphVector K a b c x y, ?_, ?_, ?_⟩
    · intro hzero
      rcases hxy with hx | hy
      · apply hx
        simpa [symmetricGraphVector] using congrFun hzero 0
      · apply hy
        simpa [symmetricGraphVector] using congrFun hzero 2
    · refine ⟨![x, y], ?_⟩
      simp [symmetricGraphLinearMap, symmetricGraphVector]
    · refine ⟨![s, t], ?_⟩
      simpa [coordinateCenterLinearMap] using hvector.symm
end CompactnessConjecture
