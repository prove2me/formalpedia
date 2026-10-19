-- Prove2me | solution 1 for CompactnessConjecture.symmetricGraphVector_mem_center_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/35151433-b307-4841-9fb6-7f26acfd225f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symmetricQuadratic_eq_bilinear

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ s t : K,
      symmetricGraphVector K a b c x y =
        s • symplecticHorizontalVector K x y +
          t • symplecticAnnihilatorVector K x y) ↔
      symmetricQuadratic a b c x y = 0 := by
  constructor
  · rintro ⟨s, t, hvector⟩
    have hzero := congrFun hvector 0
    have hone := congrFun hvector 1
    have htwo := congrFun hvector 2
    have hthree := congrFun hvector 3
    simp [symmetricGraphVector, symplecticHorizontalVector,
      symplecticAnnihilatorVector, Pi.add_apply,
      smul_eq_mul] at hzero hone htwo hthree
    have hs : s = 1 := by
      rcases hxy with hx | hy
      · have hproduct : (s - 1) * x = 0 := by
          linear_combination -hzero
        exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hx)
      · have hproduct : (s - 1) * y = 0 := by
          linear_combination -htwo
        exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hy)
    subst s
    rw [symmetricQuadratic_eq_bilinear]
    linear_combination x * hone + y * hthree
  · intro hquadratic
    have hbilinear :
        x * (a * x + b * y) + y * (b * x + c * y) = 0 := by
      simpa [symmetricQuadratic_eq_bilinear] using hquadratic
    rcases hxy with hx | hy
    · refine ⟨1, (b * x + c * y) / x, ?_⟩
      funext i
      fin_cases i
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul]
        field_simp [hx]
        linear_combination hbilinear
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul, hx]
    · refine ⟨1, -(a * x + b * y) / y, ?_⟩
      funext i
      fin_cases i
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul, hy]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul]
        field_simp [hy]
        linear_combination hbilinear
end CompactnessConjecture
