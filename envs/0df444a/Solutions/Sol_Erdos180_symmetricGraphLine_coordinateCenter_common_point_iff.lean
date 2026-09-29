-- Prove2me | solution 1 for Erdos180.symmetricGraphLine_coordinateCenter_common_point_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:05:21.142891+00:00
-- url     : https://prove2.me/submissions/539060bf-a314-4061-9fba-7a23f47f6668

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Theorems.Thm_Erdos180_symmetricQuadratic_eq_bilinear

namespace Erdos180

noncomputable section
variable (K : Type*) [Field K]

lemma symmetricGraphVector_mem_center_span_iff
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

lemma symmetricGraphLine_coordinateCenter_intersection_iff
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

end

end Erdos180

open Erdos180
variable (K : Type*) [Field K]

theorem solution
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤ (coordinateCenterLine K x y hxy).1) ↔
      symmetricQuadratic a b c x y = 0 := by
  rw [← symmetricGraphLine_coordinateCenter_intersection_iff K hxy]
  constructor
  · rintro ⟨p, hpgraph, hpcenter⟩
    have hpbot : p.1 ≠ ⊥ := by
      intro hbot
      have hrank := p.2
      rw [hbot, finrank_bot] at hrank
      omega
    obtain ⟨w, hw, hwne⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hpbot
    exact ⟨w, hwne, hpgraph hw, hpcenter hw⟩
  · rintro ⟨w, hwne, hwgraph, hwcenter⟩
    let p : SymplecticPoint K :=
      ⟨K ∙ w, finrank_span_singleton hwne⟩
    refine ⟨p, ?_, ?_⟩
    · exact (Submodule.span_le).mpr (by simpa using hwgraph)
    · exact (Submodule.span_le).mpr (by simpa using hwcenter)
