-- Prove2me | solution 1 for Esgk.thin_annulus_sq_of_noFourCocircular
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T05:13:44.236562+00:00
-- url     : https://prove2.me/submissions/5c07ac88-a587-4524-8eda-d688cf5debd4

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_PlanarGeneralPosition
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_DistanceDesign
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_ConfigurationCentroid
import Definitions.Def_Esgk_ThinAnnulus

namespace Esgk

section

open EuclideanGeometry

theorem numDistances_eq_numDistancesOrdered_of_injective {n : ℕ} {p : Config n}
    (hp : Function.Injective p) :
    NumDistances p = NumDistancesOrdered p := by
  unfold NumDistances NumDistancesOrdered OrderedDistanceValues distinctDistances Config.toFinset
  congr 1
  apply Finset.Subset.antisymm
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨pair, hpair_mem, hpair_dist⟩ := hr
    rw [Finset.mem_offDiag] at hpair_mem
    obtain ⟨hx_mem, hy_mem, hxy_ne⟩ := hpair_mem
    rw [Finset.mem_image] at hx_mem hy_mem
    obtain ⟨i, _, hpi⟩ := hx_mem
    obtain ⟨j, _, hpj⟩ := hy_mem
    rw [Finset.mem_image]
    refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
      intro (hij : i = j)
      apply hxy_ne
      rw [← hpi, ← hpj, hij]
    · simp only
      rw [hpi, hpj]
      exact hpair_dist
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨ij, hij_mem, hij_dist⟩ := hr
    rw [Finset.mem_filter] at hij_mem
    obtain ⟨_, hij_ne⟩ := hij_mem
    rw [Finset.mem_image]
    refine ⟨(p ij.1, p ij.2), ?_, hij_dist⟩
    rw [Finset.mem_offDiag]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.mem_image]; exact ⟨ij.1, Finset.mem_univ _, rfl⟩
    · rw [Finset.mem_image]; exact ⟨ij.2, Finset.mem_univ _, rfl⟩
    · intro h; exact hij_ne (hp h)

end

section

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ} {α : Type*}

theorem distanceDegreeProfile_sum_eq_pred (p : Config n) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p, (DistanceOutNeighborsAtValue p i r).card = n - 1 := by
  classical
  let s : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase i
  let f : Fin n → ℝ := fun j ↦ dist (p i) (p j)
  have hmaps : ∀ j ∈ s, f j ∈ OrderedDistanceValues p := by
    intro j hj
    rw [OrderedDistanceValues, Finset.mem_image]
    refine ⟨(i, j), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      by simpa [s, Finset.mem_erase, ne_comm] using hj⟩
  have hfiber' :
      ∑ r ∈ OrderedDistanceValues p, (s.filter (fun j ↦ f j = r)).card = s.card := by
    exact (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hcard : s.card = n - 1 := by
    simp [s, Finset.card_univ, Fintype.card_fin]
  rw [← hcard, ← hfiber']
  apply Finset.sum_congr rfl
  intro r _hr
  have hfilter : s.filter (fun j ↦ f j = r) = DistanceOutNeighborsAtValue p i r := by
    ext j
    simp [s, f, DistanceOutNeighborsAtValue, ne_comm]
  rw [hfilter]

end

section

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

lemma sum_sqDistance_expand (p : Config n) (i : Fin n) :
    ∑ j, dist (p i) (p j) ^ 2 =
      (n : ℝ) * ‖p i‖ ^ 2 + ∑ j, ‖p j‖ ^ 2 -
        2 * @inner ℝ Point _ (p i) (∑ j, p j) := by
  simp_rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left,
    inner_sub_right]
  simp_rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← inner_sum, ← sum_inner, real_inner_comm (∑ j, p j) (p i)]
  ring

lemma sum_sqDistance_eq_sum_outDegree_mul (p : Config n) (i : Fin n) :
    ∑ j, dist (p i) (p j) ^ 2 =
      ∑ r ∈ OrderedDistanceValues p,
        ((DistanceOutNeighborsAtValue p i r).card : ℝ) * r ^ 2 := by
  classical
  have hdiag : (∑ j, dist (p i) (p j) ^ 2) =
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        dist (p i) (p j) ^ 2 := by
    have h := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => dist (p i) (p j) ^ 2) (a := i) (by simp)
    simpa only [dist_self, pow_two, zero_mul, add_zero] using h.symm
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      dist (p i) (p j) ∈ OrderedDistanceValues p := by
    intro j hj
    rw [OrderedDistanceValues, Finset.mem_image]
    refine ⟨(i, j), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      by simpa [Finset.mem_erase, ne_comm] using hj⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Fin n)).erase i)
    (t := OrderedDistanceValues p)
    (g := fun j => dist (p i) (p j)) hmaps (fun r : ℝ => r ^ 2)
  rw [hdiag, ← hfiber]
  apply Finset.sum_congr rfl
  intro r _hr
  have hcard :
      (((Finset.univ : Finset (Fin n)).erase i).filter
        (fun j => dist (p i) (p j) = r)).card =
      (DistanceOutNeighborsAtValue p i r).card := by
    congr 1
    ext j
    simp [DistanceOutNeighborsAtValue, ne_comm]
  rw [← hcard]
  simp [mul_comm]

end

section

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

theorem fixedDistance_card_le_three_of_noFourCocircular {A : Config n}
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (c : Point) (r : ℝ) :
    ((Config.toFinset A).filter (fun x ↦ dist x c = r)).card ≤ 3 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Config.toFinset A).filter (fun x ↦ dist x c = r))
      (n := 4) (by omega)
  have hTA : T ⊆ Config.toFinset A := hTsub.trans (Finset.filter_subset _ _)
  have hcos : Cospherical (SetLike.coe T) := by
    refine ⟨c, r, ?_⟩
    intro x hx
    have hxT : x ∈ T := by simpa using hx
    exact (Finset.mem_filter.mp (hTsub hxT)).2
  exact hgp4 T hTA hTcard hcos

theorem distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular
    {A : Config n} (hA : Function.Injective A)
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (i : Fin n) (r : ℝ) :
    (DistanceOutNeighborsAtValue A i r).card ≤ 3 := by
  classical
  let S : Finset Point := (Config.toFinset A).filter (fun x ↦ dist x (A i) = r)
  have hcard_le : (DistanceOutNeighborsAtValue A i r).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun j ↦ A j) ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, DistanceOutNeighborsAtValue, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj
      obtain ⟨_hne, hdist⟩ := hj
      change A j ∈ (Config.toFinset A).filter (fun x ↦ dist x (A i) = r)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩,
        by simpa [dist_comm] using hdist⟩
    · intro _a _ha _b _hb hab
      exact hA hab
  exact hcard_le.trans (fixedDistance_card_le_three_of_noFourCocircular hgp4 (A i) r)

end

section

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

lemma sum_sub_configCentroid (p : Config n) (hn : 0 < n) :
    ∑ i, (p i - configCentroid p) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, configCentroid, smul_smul,
    mul_inv_cancel₀ hn0, one_smul, sub_self]

lemma sum_sqDistance_eq_centroid (p : Config n) (hn : 0 < n) (i : Fin n) :
    ∑ j, dist (p i) (p j) ^ 2 =
      (n : ℝ) * dist (p i) (configCentroid p) ^ 2 + centroidSquaredMass p := by
  have h := sum_sqDistance_expand (fun j ↦ p j - configCentroid p) i
  rw [sum_sub_configCentroid p hn, inner_zero_right, mul_zero, sub_zero] at h
  simpa only [dist_sub_right, ← dist_eq_norm, centroidSquaredMass] using h

lemma sum_distanceDegreeDeficit (p : Config n) (hn : 0 < n) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p,
      (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) =
        3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 := by
  have hdeg := distanceDegreeProfile_sum_eq_pred p i
  have hdegR :
      (∑ r ∈ OrderedDistanceValues p,
        ((DistanceOutNeighborsAtValue p i r).card : ℝ)) = (n : ℝ) - 1 := by
    rw [← Nat.cast_sum, hdeg, Nat.cast_sub (by omega)]
    norm_num
  rw [Finset.sum_sub_distrib, hdegR]
  simp only [Finset.sum_const, nsmul_eq_mul, NumDistancesOrdered]
  ring

lemma sum_weighted_distanceDegreeDeficit (p : Config n) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p,
      (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * r ^ 2 =
        3 * (∑ r ∈ OrderedDistanceValues p, r ^ 2) -
          ∑ j, dist (p i) (p j) ^ 2 := by
  rw [sum_sqDistance_eq_sum_outDegree_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

lemma weighted_distanceDegreeDeficit_le {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {B q : ℝ} (hB : 0 ≤ B)
    (hpal : ∀ r ∈ OrderedDistanceValues p, r ^ 2 ≤ B)
    (hq : 3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 ≤ q)
    (i : Fin n) :
    (∑ r ∈ OrderedDistanceValues p,
      (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * r ^ 2) ≤ q * B := by
  calc
    _ ≤ ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * B := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left (hpal r hr)
      have hc : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 3 :=
        by exact_mod_cast hcap i r
      linarith
    _ = (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) * B := by
      rw [← Finset.sum_mul, sum_distanceDegreeDeficit p hn i]
    _ ≤ q * B := mul_le_mul_of_nonneg_right hq hB

lemma distanceAnnulusRadiusSq_bounds {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) :
    0 ≤ distanceAnnulusRadiusSq p ∧
      ∀ i, dist (p i) (configCentroid p) ^ 2 ≤ distanceAnnulusRadiusSq p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hupper (i : Fin n) :
      dist (p i) (configCentroid p) ^ 2 ≤ distanceAnnulusRadiusSq p := by
    have hdef : 0 ≤ ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * r ^ 2 := by
      apply Finset.sum_nonneg
      intro r _hr
      have hc : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 3 :=
        by exact_mod_cast hcap i r
      exact mul_nonneg (by linarith) (sq_nonneg r)
    rw [sum_weighted_distanceDegreeDeficit, sum_sqDistance_eq_centroid p hn i] at hdef
    unfold distanceAnnulusRadiusSq
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  let i0 : Fin n := ⟨0, hn⟩
  exact ⟨(sq_nonneg _).trans (hupper i0), hupper⟩

lemma distanceAnnulusRadius_bounds {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) :
    0 ≤ distanceAnnulusRadius p ∧
      distanceAnnulusRadius p ^ 2 = distanceAnnulusRadiusSq p ∧
        ∀ i, dist (p i) (configCentroid p) ≤ distanceAnnulusRadius p := by
  obtain ⟨hR, hupper⟩ := distanceAnnulusRadiusSq_bounds hn hcap
  have hρ : 0 ≤ distanceAnnulusRadius p := Real.sqrt_nonneg _
  have hsq : distanceAnnulusRadius p ^ 2 = distanceAnnulusRadiusSq p :=
    Real.sq_sqrt hR
  refine ⟨hρ, hsq, ?_⟩
  intro i
  have hd := dist_nonneg (x := p i) (y := configCentroid p)
  have hi := hupper i
  nlinarith

lemma palette_sq_le_four_mul_distanceAnnulusRadiusSq {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {r : ℝ} (hr : r ∈ OrderedDistanceValues p) :
    r ^ 2 ≤ 4 * distanceAnnulusRadiusSq p := by
  obtain ⟨hρ, hsq, hupper⟩ := distanceAnnulusRadius_bounds hn hcap
  rw [OrderedDistanceValues, Finset.mem_image] at hr
  obtain ⟨⟨i, j⟩, _hij, hdist⟩ := hr
  have ht := dist_triangle (p i) (configCentroid p) (p j)
  rw [dist_comm (configCentroid p) (p j)] at ht
  have hi := hupper i
  have hj := hupper j
  have hd := dist_nonneg (x := p i) (y := p j)
  have hle : dist (p i) (p j) ≤ 2 * distanceAnnulusRadius p := by linarith
  have hsqle := mul_self_le_mul_self hd hle
  nlinarith [hdist]

theorem centroid_sq_ge_distanceAnnulusRadiusSq_mul_deficit {p : Config n}
    (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    (i : Fin n) :
    distanceAnnulusRadiusSq p *
        (1 - 4 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) / (n : ℝ)) ≤
      dist (p i) (configCentroid p) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hR := (distanceAnnulusRadiusSq_bounds hn hcap).1
  have hdef := weighted_distanceDegreeDeficit_le hn hcap
    (B := 4 * distanceAnnulusRadiusSq p) (by positivity)
    (fun _ hr ↦ palette_sq_le_four_mul_distanceAnnulusRadiusSq hn hcap hr) le_rfl i
  rw [sum_weighted_distanceDegreeDeficit, sum_sqDistance_eq_centroid p hn i] at hdef
  have hRadius : (n : ℝ) * distanceAnnulusRadiusSq p =
      3 * (∑ r ∈ OrderedDistanceValues p, r ^ 2) - centroidSquaredMass p := by
    unfold distanceAnnulusRadiusSq
    field_simp
  convert (show
      ((n : ℝ) * distanceAnnulusRadiusSq p -
        4 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) *
          distanceAnnulusRadiusSq p) / (n : ℝ) ≤
      dist (p i) (configCentroid p) ^ 2 from
        (div_le_iff₀ hnR).mpr (by nlinarith)) using 1
  field_simp

end

end Esgk

section

open EuclideanGeometry Esgk
open EuclideanGeometry
open scoped BigOperators

theorem solution {n : ℕ} {p : Config n}
    (hp : Function.Injective p)
    (hgp4 : ∀ T ⊆ Config.toFinset p, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (hn : 0 < n) {δ : ℝ}
    (hD : (NumDistances p : ℝ) ≤ (1 / 3 + δ) * (n : ℝ)) :
    ∀ i, distanceAnnulusRadiusSq p * (1 - 12 * δ - 4 / (n : ℝ)) ≤
        dist (p i) (configCentroid p) ^ 2 ∧
      dist (p i) (configCentroid p) ^ 2 ≤ distanceAnnulusRadiusSq p := by
  have hcap := distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular hp hgp4
  obtain ⟨hR, hupper⟩ := distanceAnnulusRadiusSq_bounds hn hcap
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hD' := hD
  rw [numDistances_eq_numDistancesOrdered_of_injective hp] at hD'
  have hc : 1 - 12 * δ - 4 / (n : ℝ) ≤
      1 - 4 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) / (n : ℝ) := by
    apply (mul_le_mul_iff_right₀ hnR).mp
    field_simp
    nlinarith
  intro i
  exact ⟨(mul_le_mul_of_nonneg_left hc hR).trans
    (centroid_sq_ge_distanceAnnulusRadiusSq_mul_deficit hn hcap i), hupper i⟩

end
