-- Prove2me | solution 1 for Esgk.sum_two_sub_witnesses_le
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T05:16:19.330006+00:00
-- url     : https://prove2.me/submissions/fb57ab27-440d-41ef-9081-33dbdc8e7a56

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_PlanarGeneralPosition
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_DistanceDesign
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_EquidistantWitnessCounts

namespace Esgk

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
variable {α : Type*}

theorem collinear_subset_perpBisector {a b : Point} {s : Set Point}
    [Finite s] (hab : a ≠ b) (hs : s ⊆ (AffineSubspace.perpBisector a b : Set Point)) :
    Collinear ℝ s := by
  classical
  haveI : FiniteDimensional ℝ (vectorSpan ℝ s) :=
    finiteDimensional_vectorSpan_of_finite ℝ (Set.toFinite s)
  rw [collinear_iff_finrank_le_one]
  have hspan_le : vectorSpan ℝ s ≤ (AffineSubspace.perpBisector a b).direction := by
    rw [← direction_affineSpan]
    exact AffineSubspace.direction_le (affineSpan_le.mpr hs)
  have hdir : Module.finrank ℝ (AffineSubspace.perpBisector a b).direction ≤ 1 := by
    rw [AffineSubspace.direction_perpBisector]
    have hv : b -ᵥ a ≠ (0 : Point) := vsub_ne_zero.mpr (Ne.symm hab)
    letI : Fact (Module.finrank ℝ Point = 1 + 1) := ⟨by simp [Point]⟩
    have hfin : Module.finrank ℝ (↥(ℝ ∙ (b -ᵥ a))ᗮ) = 1 := by
      simpa using
        (Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (E := Point) (n := 1) hv)
    rw [hfin]
  exact (Submodule.finrank_mono hspan_le).trans hdir

theorem equidistantWitnesses_card_le_two_of_nonTrilinear {P : Finset Point} {a b : Point}
    (hgp3 : NonTrilinear (P : Set Point)) (hab : a ≠ b) :
    (EquidistantWitnesses P a b).card ≤ 2 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := EquidistantWitnesses P a b) (n := 3) (by omega)
  have hTP : T ⊆ P := hTsub.trans (Finset.filter_subset _ _)
  rw [Finset.card_eq_three] at hTcard
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hTcard
  have hxT : x ∈ ({x, y, z} : Finset Point) := by simp
  have hyT : y ∈ ({x, y, z} : Finset Point) := by simp
  have hzT : z ∈ ({x, y, z} : Finset Point) := by simp
  have hxP : x ∈ (P : Set Point) := by exact hTP hxT
  have hyP : y ∈ (P : Set Point) := by exact hTP hyT
  have hzP : z ∈ (P : Set Point) := by exact hTP hzT
  have hxw : dist x a = dist x b := by
    have hx := hTsub hxT
    simpa [EquidistantWitnesses] using (Finset.mem_filter.mp hx).2
  have hyw : dist y a = dist y b := by
    have hy := hTsub hyT
    simpa [EquidistantWitnesses] using (Finset.mem_filter.mp hy).2
  have hzw : dist z a = dist z b := by
    have hz := hTsub hzT
    simpa [EquidistantWitnesses] using (Finset.mem_filter.mp hz).2
  have hcol : Collinear ℝ ({x, y, z} : Set Point) := by
    apply collinear_subset_perpBisector (a := a) (b := b) hab
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hxw
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hyw
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hzw
  exact (hgp3 hxP hyP hzP hxy hyz hxz) hcol

lemma indexedEquidistantWitnesses_card_le_pointWitnesses
    {n : ℕ} {p : Config n} (hp : Function.Injective p) (i j : Fin n) :
    (IndexedEquidistantWitnesses p i j).card ≤
      (EquidistantWitnesses (Config.toFinset p) (p i) (p j)).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun x => p x) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, IndexedEquidistantWitnesses,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, EquidistantWitnesses, Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, hx⟩
  · intro a _ha b _hb hab
    exact hp hab

theorem indexedEquidistantWitnesses_card_le_two_of_nonTrilinear
    {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point)) {i j : Fin n}
    (hij : i ≠ j) :
    (IndexedEquidistantWitnesses p i j).card ≤ 2 :=
  (indexedEquidistantWitnesses_card_le_pointWitnesses hp i j).trans
    (equidistantWitnesses_card_le_two_of_nonTrilinear hgp3 (hp.ne hij))

theorem fixedApex_fallingMass_eq_apexEqualDistancePairs_card
    {n : ℕ} (p : Config n) (x : Fin n) :
    (∑ r ∈ OrderedDistanceValues p,
      (DistanceOutNeighborsAtValue p x r).card *
        ((DistanceOutNeighborsAtValue p x r).card - 1)) =
      (ApexEqualDistancePairs p x).card := by
  classical
  have hmaps : ∀ ab ∈ ApexEqualDistancePairs p x,
      dist (p x) (p ab.1) ∈ OrderedDistanceValues p := by
    intro ab hab
    rw [ApexEqualDistancePairs, Finset.mem_filter, Finset.mem_offDiag] at hab
    rw [OrderedDistanceValues, Finset.mem_image]
    exact ⟨(x, ab.1), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        (Finset.mem_erase.mp hab.1.1).1.symm⟩, rfl⟩
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := fun ab : Fin n × Fin n => dist (p x) (p ab.1))
    (s := ApexEqualDistancePairs p x)
    (t := OrderedDistanceValues p) hmaps
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro r _hr
  have heq :
      (ApexEqualDistancePairs p x).filter
        (fun ab => dist (p x) (p ab.1) = r) =
      (DistanceOutNeighborsAtValue p x r).offDiag := by
    ext ab
    simp only [ApexEqualDistancePairs, Finset.mem_filter,
      Finset.mem_offDiag, DistanceOutNeighborsAtValue, Finset.mem_erase,
      Finset.mem_univ, true_and]
    aesop
  rw [heq, Finset.offDiag_card]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

theorem orderedPairWitnessTotal_eq_sum_apexEqualDistancePairs_card
    {n : ℕ} {p : Config n} (hp : Function.Injective p) :
    OrderedPairWitnessTotal p =
      ∑ x, (ApexEqualDistancePairs p x).card := by
  unfold OrderedPairWitnessTotal IndexedEquidistantWitnesses
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  have heq :
      ((Finset.univ : Finset (Fin n)).offDiag).filter
        (fun ab => dist (p x) (p ab.1) = dist (p x) (p ab.2)) =
      ApexEqualDistancePairs p x := by
    ext ab
    rw [ApexEqualDistancePairs, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hoff, hdist⟩
      rw [Finset.mem_offDiag] at hoff
      obtain ⟨ha, hb, hab⟩ := hoff
      have hax : ab.1 ≠ x := by
        intro h
        have hzero : dist (p x) (p ab.2) = 0 := by
          simpa [h] using hdist.symm
        exact hab (h.trans (hp (dist_eq_zero.mp hzero)))
      have hbx : ab.2 ≠ x := by
        intro h
        have hzero : dist (p x) (p ab.1) = 0 := by
          simpa [h] using hdist
        have hxa : x = ab.1 := hp (dist_eq_zero.mp hzero)
        exact hab (hxa.symm.trans h.symm)
      refine ⟨?_, hdist⟩
      rw [Finset.mem_offDiag]
      exact ⟨Finset.mem_erase.mpr ⟨hax, ha⟩,
        Finset.mem_erase.mpr ⟨hbx, hb⟩, hab⟩
    · rintro ⟨hoff, hdist⟩
      refine ⟨?_, hdist⟩
      rw [Finset.mem_offDiag] at hoff ⊢
      exact ⟨(Finset.mem_erase.mp hoff.1).2,
        (Finset.mem_erase.mp hoff.2.1).2, hoff.2.2⟩
  rw [← heq]
  rw [Finset.sum_filter]

theorem distanceDegreeFallingMass_eq_orderedPairWitnessTotal
    {n : ℕ} {p : Config n} (hp : Function.Injective p) :
    DistanceDegreeFallingMass p = OrderedPairWitnessTotal p := by
  unfold DistanceDegreeFallingMass
  rw [Finset.sum_comm]
  calc
    (∑ x, ∑ r ∈ OrderedDistanceValues p,
      (DistanceOutNeighborsAtValue p x r).card *
        ((DistanceOutNeighborsAtValue p x r).card - 1)) =
        ∑ x, (ApexEqualDistancePairs p x).card := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact fixedApex_fallingMass_eq_apexEqualDistancePairs_card p x
    _ = OrderedPairWitnessTotal p :=
      (orderedPairWitnessTotal_eq_sum_apexEqualDistancePairs_card hp).symm

end

section

open EuclideanGeometry
variable {n : ℕ}

private theorem four_mul_sub_six_le_falling (d : ℕ) :
    4 * (d : ℝ) - 6 ≤ ((d * (d - 1) : ℕ) : ℝ) := by
  have h : 4 * d ≤ d * (d - 1) + 6 := by
    rcases Nat.lt_or_ge d 3 with hd | hd
    · interval_cases d <;> norm_num
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
      have hk : (3 + k) * (3 + k - 1) = k * k + 5 * k + 6 := by
        rw [show 3 + k - 1 = k + 2 by omega]
        ring
      omega
  have h' : ((4 * d : ℕ) : ℝ) ≤ ((d * (d - 1) + 6 : ℕ) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_add] at h'
  push_cast at h' ⊢
  linarith

theorem orderedPairWitnessTotal_lower_bound {p : Config n} (hp : Function.Injective p) :
    (n : ℝ) * (4 * ((n : ℝ) - 1) - 6 * (NumDistancesOrdered p : ℝ)) ≤
      (OrderedPairWitnessTotal p : ℝ) := by
  rw [← distanceDegreeFallingMass_eq_orderedPairWitnessTotal hp, DistanceDegreeFallingMass,
    Finset.sum_comm]
  have hrow : ∀ x : Fin n, 4 * ((n : ℝ) - 1) - 6 * (NumDistancesOrdered p : ℝ) ≤
      ((∑ r ∈ OrderedDistanceValues p, (DistanceOutNeighborsAtValue p x r).card *
        ((DistanceOutNeighborsAtValue p x r).card - 1) : ℕ) : ℝ) := by
    intro x
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Fin.pos x).ne'
    have hsum : ((∑ r ∈ OrderedDistanceValues p,
        (DistanceOutNeighborsAtValue p x r).card : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [distanceDegreeProfile_sum_eq_pred p x, Nat.cast_sub hn, Nat.cast_one]
    rw [Nat.cast_sum] at hsum ⊢
    calc 4 * ((n : ℝ) - 1) - 6 * (NumDistancesOrdered p : ℝ)
        = ∑ r ∈ OrderedDistanceValues p,
            (4 * ((DistanceOutNeighborsAtValue p x r).card : ℝ) - 6) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
            NumDistancesOrdered, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum fun r _ ↦ four_mul_sub_six_le_falling _
  calc (n : ℝ) * (4 * ((n : ℝ) - 1) - 6 * (NumDistancesOrdered p : ℝ))
      = ∑ _x : Fin n, (4 * ((n : ℝ) - 1) - 6 * (NumDistancesOrdered p : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ x : Fin n, ((∑ r ∈ OrderedDistanceValues p,
          (DistanceOutNeighborsAtValue p x r).card *
            ((DistanceOutNeighborsAtValue p x r).card - 1) : ℕ) : ℝ) :=
        Finset.sum_le_sum fun x _ ↦ hrow x
    _ = _ := by rw [Nat.cast_sum]

end

end Esgk

section

open EuclideanGeometry Esgk
open EuclideanGeometry

theorem solution {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    {Φ : Finset (Fin n × Fin n)} (hΦ : Φ ⊆ (Finset.univ : Finset (Fin n)).offDiag) :
    ∑ ab ∈ Φ, (2 - ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ)) ≤
      2 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) := by
  have hWle : ∀ ab ∈ (Finset.univ : Finset (Fin n)).offDiag,
      ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) ≤ 2 := by
    intro ab hab
    exact_mod_cast indexedEquidistantWitnesses_card_le_two_of_nonTrilinear hp hgp3
      (Finset.mem_offDiag.mp hab).2.2
  have hdef : ∑ ab ∈ Φ,
        (2 - ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ)) ≤
      ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag,
        (2 - ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hΦ fun ab hab _ ↦ by
      linarith [hWle ab hab]
  have hcard : (((Finset.univ : Finset (Fin n)).offDiag.card : ℕ) : ℝ) =
      (n : ℝ) * n - n := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.le_mul_self n), Nat.cast_mul]
  have htot : ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag,
      ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) =
        (OrderedPairWitnessTotal p : ℝ) := by
    rw [OrderedPairWitnessTotal, Nat.cast_sum]
  rw [Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin n)).offDiag),
    Finset.sum_const, nsmul_eq_mul, htot, hcard] at hdef
  have hlow := orderedPairWitnessTotal_lower_bound hp
  linarith

end
