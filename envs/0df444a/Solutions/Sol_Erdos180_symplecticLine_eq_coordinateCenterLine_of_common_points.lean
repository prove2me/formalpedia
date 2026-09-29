-- Prove2me | solution 1 for Erdos180.symplecticLine_eq_coordinateCenterLine_of_common_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:12:25.764209+00:00
-- url     : https://prove2.me/submissions/934d6463-cf34-4e91-9f87-893ba811e020

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Theorems.Thm_Erdos180_symplecticPoint_sup_finrank

namespace Erdos180

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

lemma symplecticCanonicalLines_disjoint :
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

lemma symplecticVertical_mem_coordinateCenter_of_orthogonal
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

end

end Erdos180

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    (C : SymplecticLine K)
    (p q : SymplecticPoint K)
    (hpH : p.1 ≤ (symmetricGraphLine K 0 0 0).1)
    (hpC : p.1 ≤ C.1)
    (hqV : q.1 ≤ (symplecticVerticalLine K).1)
    (hqC : q.1 ≤ C.1) :
    ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
      C = coordinateCenterLine K x y hxy := by
  have hpos : 0 < Module.finrank K p.1 := by
    rw [p.2]
    norm_num
  obtain ⟨u, hu⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have huhorizontal := hpH u.2
  change
    (u : SymplecticVector K) ∈
      LinearMap.range (symmetricGraphLinearMap K 0 0 0)
    at huhorizontal
  obtain ⟨z, hz⟩ := huhorizontal
  have hu1 : (u : SymplecticVector K) 1 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      (congrFun hz 1).symm
  have hu3 : (u : SymplecticVector K) 3 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      (congrFun hz 3).symm
  let x : K := (u : SymplecticVector K) 0
  let y : K := (u : SymplecticVector K) 2
  have huvector :
      (u : SymplecticVector K) =
        symplecticHorizontalVector K x y := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, x, y, hu1, hu3]
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    have hx : x = 0 :=
      Classical.byContradiction (fun hx => h (Or.inl hx))
    have hy : y = 0 :=
      Classical.byContradiction (fun hy => h (Or.inr hy))
    have huzero : (u : SymplecticVector K) = 0 := by
      rw [huvector, hx, hy]
      simp [symplecticHorizontalVector]
    apply hu
    apply Subtype.ext
    simpa using huzero
  have hpq : p ≠ q := by
    intro heq
    subst q
    have hbot :
        (u : SymplecticVector K) ∈
          (⊥ : Submodule K (SymplecticVector K)) :=
      (symplecticCanonicalLines_disjoint K).le_bot
        ⟨hpH u.2, hqV u.2⟩
    apply hu
    apply Subtype.ext
    simpa using hbot
  have hucenter :
      (u : SymplecticVector K) ∈
        (coordinateCenterLine K x y hxy).1 := by
    change
      (u : SymplecticVector K) ∈
        LinearMap.range (coordinateCenterLinearMap K x y)
    refine ⟨![1, 0], ?_⟩
    rw [huvector]
    simp [coordinateCenterLinearMap,
      symplecticHorizontalVector,
      symplecticAnnihilatorVector, smul_eq_mul]
  have hpcenter :
      p.1 ≤ (coordinateCenterLine K x y hxy).1 := by
    intro v hv
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      p.2 hu (⟨v, hv⟩ : p.1)
    have hav : a • (u : SymplecticVector K) = v :=
      congrArg Subtype.val ha
    rw [← hav]
    exact (coordinateCenterLine K x y hxy).1.smul_mem a hucenter
  have hqcenter :
      q.1 ≤ (coordinateCenterLine K x y hxy).1 := by
    intro v hv
    apply symplecticVertical_mem_coordinateCenter_of_orthogonal
      K hxy (hqV hv)
    rw [← huvector]
    exact C.2.2 (u : SymplecticVector K)
      (hpC u.2) v (hqC hv)
  refine ⟨x, y, hxy, ?_⟩
  apply Subtype.ext
  have hspanC : p.1 ⊔ q.1 = C.1 :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hpC hqC)
      ((symplecticPoint_sup_finrank K hpq).trans C.2.1.symm)
  have hspanCenter :
      p.1 ⊔ q.1 = (coordinateCenterLine K x y hxy).1 :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hpcenter hqcenter)
      ((symplecticPoint_sup_finrank K hpq).trans
        (coordinateCenterLine K x y hxy).2.1.symm)
  exact hspanC.symm.trans hspanCenter
