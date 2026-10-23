-- Prove2me | solution 1 for CircletTSP.Facet.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:09:09.009147+00:00
-- url     : https://prove2.me/submissions/00cf524f-4924-4a51-91e8-8c4a34861a77

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

set_option autoImplicit false

open scoped BigOperators

namespace CircletTSP.Facet.TourCounts

lemma rotate_ne_self {n : ℕ} (hn : 1 < n) (i : Fin n) : finRotate n i ≠ i := by
  cases n with
  | zero => omega
  | succ n =>
    intro h
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    by_cases hi : i = Fin.last n
    · subst i
      simp at hv
      omega
    · simp [hi] at hv

lemma tourVec_nonneg {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    0 ≤ MetricTSP.tourVec π u v := by
  unfold MetricTSP.tourVec
  positivity

lemma tourVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = MetricTSP.tourVec π v u := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps, or_comm]

lemma tourVec_eq_step_sum {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = ∑ k : Fin n,
      if (π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u)
      then (1 : ℝ) else 0 := by
  unfold MetricTSP.tourVec MetricTSP.tourSteps
  exact Finset.natCast_card_filter _ _

lemma single_edge_mass_of_lt {n : ℕ} (a b : Fin n) (hab : a < b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then (1 : ℝ) else 0) = 1 := by
  have heq (u v : Fin n) :
      (u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ↔ u = a ∧ v = b := by
    constructor
    · rintro ⟨huv, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨rfl, rfl⟩
      · exact (lt_asymm hab huv).elim
    · rintro ⟨rfl, rfl⟩
      exact ⟨hab, Or.inl ⟨rfl, rfl⟩⟩
  simp_rw [heq]
  simp [ite_and]

lemma single_edge_mass {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then (1 : ℝ) else 0) = 1 := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact single_edge_mass_of_lt a b h
  · simpa [or_comm, and_comm] using single_edge_mass_of_lt b a h

lemma tour_unordered_mass {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) :
    (∑ u : Fin n, ∑ v : Fin n, if u < v then MetricTSP.tourVec π u v else 0) = n := by
  have hexpand (u v : Fin n) :
      (if u < v then MetricTSP.tourVec π u v else 0) =
      ∑ k : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by
    rw [tourVec_eq_step_sum]
    by_cases huv : u < v <;> simp [huv]
  simp_rw [hexpand]
  calc
    _ = ∑ u : Fin n, ∑ k : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ u : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by rw [Finset.sum_comm]
    _ = ∑ _k : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      apply single_edge_mass
      intro h
      exact rotate_ne_self hn k (π.injective h).symm
    _ = n := by simp

lemma cycLen_mem_range_of_lt {n : ℕ} (u v : Fin n) (huv : u < v) :
    cycLen n u v ∈ Finset.Icc 1 (n / 2) := by
  have hu := u.isLt
  have hv := v.isLt
  have huv' : u.val < v.val := huv
  simp only [Finset.mem_Icc, cycLen,
    Int.natAbs_natCast_sub_natCast_of_le (Nat.le_of_lt huv')]
  omega

lemma sum_lenCount_eq_mass (n : ℕ) (x : Fin n → Fin n → ℝ) :
    (∑ i ∈ Finset.Icc 1 (n / 2), lenCount n i x) =
      ∑ u : Fin n, ∑ v : Fin n, if u < v then x u v else 0 := by
  unfold lenCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : u < v
  · have hmem := cycLen_mem_range_of_lt u v huv
    simp [huv, hmem]
  · simp [huv]

lemma sum_lenCount_tour {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) :
    (∑ i ∈ Finset.Icc 1 (n / 2), lenCount n i (MetricTSP.tourVec π)) = n := by
  rw [sum_lenCount_eq_mass]
  exact tour_unordered_mass hn π

lemma lenCount_nonneg {n : ℕ} (π : Equiv.Perm (Fin n)) (i : ℕ) :
    0 ≤ lenCount n i (MetricTSP.tourVec π) := by
  unfold lenCount
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · exact tourVec_nonneg π u v
  · exact le_rfl

end CircletTSP.Facet.TourCounts

namespace CircletTSP.Facet.TourCounts

lemma tourVec_eq_successors {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) (huv : u ≠ v) :
    MetricTSP.tourVec π u v =
      (if π (finRotate n (π.symm u)) = v then 1 else 0) +
      (if π (finRotate n (π.symm v)) = u then 1 else 0) := by
  rw [tourVec_eq_step_sum]
  have hsplit (k : Fin n) :
      (if (π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u)
        then (1 : ℝ) else 0) =
      (if k = π.symm u then if π (finRotate n k) = v then 1 else 0 else 0) +
      (if k = π.symm v then if π (finRotate n k) = u then 1 else 0 else 0) := by
    have hku : π k = u ↔ k = π.symm u := π.eq_symm_apply.symm
    have hkv : π k = v ↔ k = π.symm v := π.eq_symm_apply.symm
    simp only [hku, hkv]
    by_cases hu : k = π.symm u
    · by_cases hv : k = π.symm v
      · exact (huv (π.symm.injective (hu.symm.trans hv))).elim
      · simp [hu, huv]
    · by_cases hv : k = π.symm v
      · simp [hv, Ne.symm huv]
      · simp [hu, hv]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp

lemma tourVec_diagonal_zero {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    MetricTSP.tourVec π u u = 0 := by
  rw [tourVec_eq_step_sum]
  apply Finset.sum_eq_zero
  intro k _
  have hnot : ¬ (π k = u ∧ π (finRotate n k) = u) := by
    rintro ⟨ha, hb⟩
    exact rotate_ne_self hn k (π.injective (hb.trans ha.symm))
  simp only [or_self, if_neg hnot]

def successorPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  π.symm.trans ((finRotate n).trans π)

lemma successor_ne_self {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    successorPerm π u ≠ u := by
  intro h
  have h' : finRotate n (π.symm u) = π.symm u := by
    apply π.injective
    simpa [successorPerm] using h
  exact rotate_ne_self hn (π.symm u) h'

lemma tourVec_eq_successors_all {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v =
      (if successorPerm π u = v then 1 else 0) +
      (if successorPerm π v = u then 1 else 0) := by
  by_cases huv : u = v
  · subst v
    simp [tourVec_diagonal_zero hn, successor_ne_self hn]
  · exact tourVec_eq_successors π u v huv

lemma tourVec_row_sum {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    (∑ v : Fin n, MetricTSP.tourVec π u v) = 2 := by
  simp_rw [tourVec_eq_successors_all hn]
  rw [Finset.sum_add_distrib]
  have hleft : (∑ v : Fin n, if successorPerm π u = v then (1 : ℝ) else 0) = 1 := by simp
  have hright : (∑ v : Fin n, if successorPerm π v = u then (1 : ℝ) else 0) = 1 := by
    simp_rw [← (successorPerm π).eq_symm_apply]
    simp
  rw [hleft, hright]
  norm_num

lemma tourVec_trans {n : ℕ} (π σ : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec (π.trans σ) (σ u) (σ v) = MetricTSP.tourVec π u v := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps]

end CircletTSP.Facet.TourCounts

namespace CircletTSP.Facet.Counterbound

lemma coefficient_lower_nat (n i : ℕ) (h4 : 4 ∣ n) (hi : i ∈ Finset.Icc 1 (n / 2)) :
    2 ≤ coeff n i + (if i = 1 then 1 else 0) + (if i = n / 2 then 2 else 0) := by
  have hnmod : n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
  unfold coeff
  split_ifs <;> omega

lemma cost_lower (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (x : Fin n → Fin n → ℝ)
    (hx : ∀ i, 0 ≤ lenCount n i x) :
    2 * (∑ i ∈ Finset.Icc 1 (n / 2), lenCount n i x) ≤
      circletForm n x + lenCount n 1 x + 2 * lenCount n (n / 2) x := by
  have hnmod : n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  have h1mem : 1 ∈ Finset.Icc 1 (n / 2) := by simp only [Finset.mem_Icc]; omega
  have hdmem : n / 2 ∈ Finset.Icc 1 (n / 2) := by simp only [Finset.mem_Icc]; omega
  have hterm (i : ℕ) (hi : i ∈ Finset.Icc 1 (n / 2)) :
      2 * lenCount n i x ≤ (coeff n i : ℝ) * lenCount n i x +
        (if i = 1 then lenCount n i x else 0) +
        (if i = n / 2 then 2 * lenCount n i x else 0) := by
    have hc : (2 : ℝ) ≤ (coeff n i : ℝ) +
        (if i = 1 then 1 else 0) + (if i = n / 2 then 2 else 0) := by
      exact_mod_cast coefficient_lower_nat n i h4 hi
    calc
      2 * lenCount n i x ≤ ((coeff n i : ℝ) +
          (if i = 1 then 1 else 0) + (if i = n / 2 then 2 else 0)) * lenCount n i x :=
        mul_le_mul_of_nonneg_right hc (hx i)
      _ = _ := by split_ifs <;> ring
  have hsum := Finset.sum_le_sum hterm
  simpa [circletForm, Finset.sum_add_distrib, ← Finset.mul_sum, h1mem, hdmem] using hsum

end CircletTSP.Facet.Counterbound

open CircletTSP.Facet

theorem solution (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n))
    (hlt : circletForm n (MetricTSP.tourVec π) < (n : ℝ) - 2) :
    lenCount n 1 (MetricTSP.tourVec π) + 2 * lenCount n (n / 2) (MetricTSP.tourVec π) >
      (n : ℝ) + 2 := by
  have hnmod : n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  have hn2 : 1 < n := by omega
  have hcost := Counterbound.cost_lower n hn h4 (MetricTSP.tourVec π)
    (TourCounts.lenCount_nonneg π)
  rw [TourCounts.sum_lenCount_tour hn2 π] at hcost
  linarith
