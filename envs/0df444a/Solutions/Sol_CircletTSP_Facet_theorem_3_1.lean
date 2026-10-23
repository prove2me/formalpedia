-- Prove2me | solution 1 for CircletTSP.Facet.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:12:32.59202+00:00
-- url     : https://prove2.me/submissions/fa61b584-56e0-40a2-8904-34933bf250a1

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting
import Theorems.Thm_CircletTSP_Facet_claim_4_1
import Theorems.Thm_CircletTSP_Facet_claim_4_2
import Theorems.Thm_CircletTSP_Facet_window_count
import Theorems.Thm_CircletTSP_Facet_contraction_step

set_option autoImplicit false
open scoped BigOperators

namespace CircletTSP.Facet.Base4

def unitEdges (π : Equiv.Perm (Fin 4)) : ℕ :=
  ∑ u : Fin 4, ∑ v : Fin 4,
    if u < v ∧ cycLen 4 u v = 1 then (MetricTSP.tourSteps π u v).card else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma two_le_unitEdges : ∀ π : Equiv.Perm (Fin 4), 2 ≤ unitEdges π := by
  decide

lemma form_eq (π : Equiv.Perm (Fin 4)) :
    circletForm 4 (MetricTSP.tourVec π) = (unitEdges π : ℝ) := by
  norm_num [circletForm, coeff, Finset.sum_Icc_succ_top]
  simp [lenCount, MetricTSP.tourVec, unitEdges]

end CircletTSP.Facet.Base4

open CircletTSP.Facet

theorem CircletTSP.Facet.Base4.base_case (π : Equiv.Perm (Fin 4)) :
    (4 : ℝ) - 2 ≤ circletForm 4 (MetricTSP.tourVec π) := by
  rw [Base4.form_eq]
  norm_num
  exact_mod_cast Base4.two_le_unitEdges π

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

theorem CircletTSP.Facet.Counterbound.counterbound (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n))
    (hlt : circletForm n (MetricTSP.tourVec π) < (n : ℝ) - 2) :
    lenCount n 1 (MetricTSP.tourVec π) + 2 * lenCount n (n / 2) (MetricTSP.tourVec π) >
      (n : ℝ) + 2 := by
  have hnmod : n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  have hn2 : 1 < n := by omega
  have hcost := Counterbound.cost_lower n hn h4 (MetricTSP.tourVec π)
    (TourCounts.lenCount_nonneg π)
  rw [TourCounts.sum_lenCount_tour hn2 π] at hcost
  linarith

namespace CircletTSP.Facet.WindowBoundProof

lemma rotate_twice_ne_self {n : ℕ} (hn : 2 < n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  let : NeZero n := ⟨by omega⟩
  intro h
  have hv := congrArg Fin.val h
  simp only [finRotate_apply, Fin.val_add, Fin.val_one'] at hv
  rw [Nat.mod_eq_of_lt (show 1 < n by omega)] at hv
  have hi := i.isLt
  by_cases h₁ : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h₁] at hv
    by_cases h₂ : i.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt h₂] at hv
      omega
    · have heq : i.val + 1 + 1 = n := by omega
      rw [heq, Nat.mod_self] at hv
      omega
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (show 1 < n by omega)] at hv
    omega

lemma tourVec_zero_or_one {n : ℕ} (hn : 2 < n) (π : Equiv.Perm (Fin n))
    (u v : Fin n) : MetricTSP.tourVec π u v = 0 ∨ MetricTSP.tourVec π u v = 1 := by
  have hc : (MetricTSP.tourSteps π u v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    simp only [MetricTSP.tourSteps, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rcases hi with ⟨hiu, hiv⟩ | ⟨hiv, hiu⟩ <;>
      rcases hj with ⟨hju, hjv⟩ | ⟨hjv, hju⟩
    · exact π.injective (hiu.trans hju.symm)
    · have h₁ : finRotate n i = j := π.injective (hiv.trans hjv.symm)
      have h₂ : finRotate n j = i := π.injective (hju.trans hiu.symm)
      exact (rotate_twice_ne_self hn i (by rw [h₁, h₂])).elim
    · have h₁ : finRotate n i = j := π.injective (hiu.trans hju.symm)
      have h₂ : finRotate n j = i := π.injective (hjv.trans hiv.symm)
      exact (rotate_twice_ne_self hn i (by rw [h₁, h₂])).elim
    · exact π.injective (hiv.trans hjv.symm)
  have heq : (MetricTSP.tourSteps π u v).card = 0 ∨
      (MetricTSP.tourSteps π u v).card = 1 := by omega
  simpa only [MetricTSP.tourVec, Nat.cast_eq_zero, Nat.cast_eq_one] using heq

lemma tourVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = MetricTSP.tourVec π v u := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps, or_comm]

lemma shift_shift {n : ℕ} (u : Fin n) (a b : ℕ) :
    shift (shift u a) b = shift u (a + b) := by
  apply Fin.ext
  change ((u.val + a) % n + b) % n = (u.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma shift_add_n {n : ℕ} (u : Fin n) (a : ℕ) : shift u (a + n) = shift u a := by
  apply Fin.ext
  simp [shift, Nat.add_mod]

lemma shift_zero {n : ℕ} (u : Fin n) : shift u 0 = u := by
  apply Fin.ext
  simpa only [shift, Nat.add_zero] using Nat.mod_eq_of_lt u.isLt

lemma window_le_two_direct (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n)
    (π : Equiv.Perm (Fin n))
    (hno : ∀ u : Fin n, ¬ IsStructA π u ∧ ¬ IsStructB1 π u ∧ ¬ IsStructB2 π u) :
    ∀ u : Fin n, window π u ≤ 2 := by
  intro u
  have hn3 : 2 < n := by omega
  have hd : n / 2 + n / 2 = n := by omega
  have hs₀ : shift (shift u (n / 2)) (n / 2) = u := by
    rw [shift_shift, hd]
    simpa only [Nat.zero_add, shift_zero] using shift_add_n u 0
  have hs₁ : shift (shift u (n / 2)) 1 = shift u (n / 2 + 1) := shift_shift _ _ _
  have hs₂ : shift (shift u (n / 2)) (1 + n / 2) = shift u 1 := by
    rw [shift_shift, show n / 2 + (1 + n / 2) = 1 + n by omega, shift_add_n]
  have hA : ¬ (MetricTSP.tourVec π u (shift u 1) = 1 ∧
      MetricTSP.tourVec π u (shift u (n / 2)) = 1 ∧
      MetricTSP.tourVec π (shift u 1) (shift u (1 + n / 2)) = 1) := by
    rintro ⟨hp, hr, hs⟩
    apply (hno u).1
    exact ⟨(tourVec_symm π _ _).trans hr, hp, hs⟩
  have hB₁ : ¬ (MetricTSP.tourVec π u (shift u 1) = 1 ∧
      MetricTSP.tourVec π (shift u (n / 2)) (shift u (n / 2 + 1)) = 1 ∧
      MetricTSP.tourVec π u (shift u (n / 2)) = 1) := by
    rintro ⟨hp, hq, hr⟩
    apply (hno u).2.1
    exact ⟨(tourVec_symm π _ _).trans hp, hr, by simpa [Adj, Nat.add_comm] using hq⟩
  have hB₂ : ¬ (MetricTSP.tourVec π u (shift u 1) = 1 ∧
      MetricTSP.tourVec π (shift u (n / 2)) (shift u (n / 2 + 1)) = 1 ∧
      MetricTSP.tourVec π (shift u 1) (shift u (1 + n / 2)) = 1) := by
    rintro ⟨hp, hq, hs⟩
    apply (hno u).2.2
    exact ⟨hp, hs, by simpa [Adj, Nat.add_comm] using (tourVec_symm π _ _).trans hq⟩
  have hA' : ¬ (MetricTSP.tourVec π (shift u (n / 2)) (shift u (n / 2 + 1)) = 1 ∧
      MetricTSP.tourVec π u (shift u (n / 2)) = 1 ∧
      MetricTSP.tourVec π (shift u 1) (shift u (1 + n / 2)) = 1) := by
    rintro ⟨hq, hr, hs⟩
    apply (hno (shift u (n / 2))).1
    simp only [IsStructA, Adj, hs₀, hs₁, hs₂]
    exact ⟨hr, hq, by simpa [Nat.add_comm] using (tourVec_symm π _ _).trans hs⟩
  rcases tourVec_zero_or_one hn3 π u (shift u 1) with hp | hp <;>
    rcases tourVec_zero_or_one hn3 π (shift u (n / 2)) (shift u (n / 2 + 1)) with hq | hq <;>
    rcases tourVec_zero_or_one hn3 π u (shift u (n / 2)) with hr | hr <;>
    rcases tourVec_zero_or_one hn3 π (shift u 1) (shift u (1 + n / 2)) with hs | hs <;>
    simp_all [window] <;> norm_num

end CircletTSP.Facet.WindowBoundProof

namespace CircletTSP.Facet.PathExtension

open WindowBoundProof
open Fin.NatCast

lemma adj_symm {n : ℕ} {π : Equiv.Perm (Fin n)} {u v : Fin n} (h : Adj π u v) :
    Adj π v u := (tourVec_symm π _ _).trans h

lemma adj_step {n : ℕ} (hn : 2 < n) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    Adj π (π i) (π (finRotate n i)) := by
  have hmem : i ∈ MetricTSP.tourSteps π (π i) (π (finRotate n i)) := by
    simp [MetricTSP.tourSteps]
  have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
  rcases tourVec_zero_or_one hn π (π i) (π (finRotate n i)) with h | h
  · have hz : (MetricTSP.tourSteps π (π i) (π (finRotate n i))).card = 0 := by
      exact_mod_cast (show ((MetricTSP.tourSteps π (π i) (π (finRotate n i))).card : ℝ) = 0 from h)
    omega
  · exact h

lemma adj_iff_indices {n : ℕ} [NeZero n] (hn : 2 < n) (π : Equiv.Perm (Fin n))
    (u v : Fin n) :
    Adj π u v ↔ π.symm v = π.symm u + 1 ∨ π.symm u = π.symm v + 1 := by
  constructor
  · intro h
    have hcard : (MetricTSP.tourSteps π u v).card = 1 := by
      exact_mod_cast (show ((MetricTSP.tourSteps π u v).card : ℝ) = 1 from h)
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < (MetricTSP.tourSteps π u v).card)
    simp only [MetricTSP.tourSteps, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [finRotate_apply]
  · intro h
    rcases h with h | h
    · have hh := adj_step hn π (π.symm u)
      simpa only [finRotate_apply, ← h, Equiv.apply_symm_apply] using hh
    · have hh := adj_symm (adj_step hn π (π.symm v))
      simpa only [finRotate_apply, ← h, Equiv.apply_symm_apply] using hh

lemma offset_injective {n : ℕ} [NeZero n] (i : Fin n) {a b : ℕ}
    (ha : a < n) (hb : b < n) (h : i + (a : Fin n) = i + (b : Fin n)) : a = b := by
  have hv := congrArg Fin.val (add_left_cancel h)
  simpa only [Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv

lemma forward_extend {n : ℕ} [NeZero n] (hn : 4 < n) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    ∃ j k : Fin n,
      (∀ l : ℕ, l < 4 → j ≠ π (i + (l : Fin n))) ∧
      (∀ l : ℕ, l < 4 → k ≠ π (i + (l : Fin n))) ∧
      Adj π j (π i) ∧ Adj π (π (i + 3)) k := by
  refine ⟨π (i - 1), π (i + 4), ?_, ?_, ?_, ?_⟩
  · intro l hl h
    have heq := π.injective h
    have heq' : i + (0 : Fin n) = i + ((l + 1 : ℕ) : Fin n) := by
      rw [Nat.cast_add, Nat.cast_one]
      calc
        _ = (i - 1) + 1 := by abel
        _ = (i + (l : Fin n)) + 1 := by rw [heq]
        _ = _ := by abel
    have := offset_injective (a := 0) (b := l + 1) i (by omega) (by omega) heq'
    omega
  · intro l hl h
    have := offset_injective i hn (show l < n by omega) (π.injective h)
    omega
  · have hh := adj_step (by omega : 2 < n) π (i - 1)
    simpa only [finRotate_apply, sub_add_cancel] using hh
  · have hh := adj_step (by omega : 2 < n) π (i + 3)
    convert hh using 1
    rw [finRotate_apply]
    congr 1
    norm_num [add_assoc]

lemma path_indices {n : ℕ} [NeZero n] (hn : 2 < n) (π : Equiv.Perm (Fin n))
    (a b c d : Fin n) (hac : a ≠ c) (hbd : b ≠ d)
    (hab : Adj π a b) (hbc : Adj π b c) (hcd : Adj π c d) :
    (π.symm b = π.symm a + 1 ∧ π.symm c = π.symm a + 2 ∧
      π.symm d = π.symm a + 3) ∨
    (π.symm c = π.symm d + 1 ∧ π.symm b = π.symm d + 2 ∧
      π.symm a = π.symm d + 3) := by
  have hac' : π.symm a ≠ π.symm c := fun h => hac (π.symm.injective h)
  have hbd' : π.symm b ≠ π.symm d := fun h => hbd (π.symm.injective h)
  rcases (adj_iff_indices hn π a b).mp hab with hab | hab <;>
    rcases (adj_iff_indices hn π b c).mp hbc with hbc | hbc <;>
    rcases (adj_iff_indices hn π c d).mp hcd with hcd | hcd
  · left
    refine ⟨hab, ?_, ?_⟩
    · rw [hbc, hab]
      norm_num [add_assoc]
    · rw [hcd, hbc, hab]
      norm_num [add_assoc]
  · exact (hbd' (add_right_cancel (hbc.symm.trans hcd))).elim
  · exact (hac' (add_right_cancel (hab.symm.trans hbc))).elim
  · exact (hac' (add_right_cancel (hab.symm.trans hbc))).elim
  · exact (hac' (hab.trans hbc.symm)).elim
  · exact (hac' (hab.trans hbc.symm)).elim
  · exact (hbd' (hbc.trans hcd.symm)).elim
  · right
    refine ⟨hcd, ?_, ?_⟩
    · rw [hbc, hcd]
      norm_num [add_assoc]
    · rw [hab, hbc, hcd]
      norm_num [add_assoc]

lemma four_path_extend {n : ℕ} (hn : 4 < n) (π : Equiv.Perm (Fin n))
    (a b c d : Fin n) (hac : a ≠ c) (hbd : b ≠ d)
    (hab : Adj π a b) (hbc : Adj π b c) (hcd : Adj π c d) :
    ∃ j k : Fin n,
      (j ≠ a ∧ j ≠ b ∧ j ≠ c ∧ j ≠ d) ∧
      (k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ k ≠ d) ∧ Adj π j a ∧ Adj π d k := by
  let : NeZero n := ⟨by omega⟩
  have forward (a b c d : Fin n)
      (hb : π.symm b = π.symm a + 1) (hc : π.symm c = π.symm a + 2)
      (hd : π.symm d = π.symm a + 3) :
      ∃ j k : Fin n,
        (j ≠ a ∧ j ≠ b ∧ j ≠ c ∧ j ≠ d) ∧
        (k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ k ≠ d) ∧ Adj π j a ∧ Adj π d k := by
    obtain ⟨j, k, hj, hk, hja, hdk⟩ := forward_extend hn π (π.symm a)
    have hb' : π (π.symm a + 1) = b := by rw [← hb, Equiv.apply_symm_apply]
    have hc' : π (π.symm a + 2) = c := by rw [← hc, Equiv.apply_symm_apply]
    have hd' : π (π.symm a + 3) = d := by rw [← hd, Equiv.apply_symm_apply]
    refine ⟨j, k, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero, Equiv.apply_symm_apply, hb', hc', hd'] using
        And.intro (hj 0 (by decide)) (And.intro (hj 1 (by decide)) (And.intro (hj 2 (by decide)) (hj 3 (by decide))))
    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero, Equiv.apply_symm_apply, hb', hc', hd'] using
        And.intro (hk 0 (by decide)) (And.intro (hk 1 (by decide)) (And.intro (hk 2 (by decide)) (hk 3 (by decide))))
    · simpa only [Equiv.apply_symm_apply] using hja
    · simpa only [hd'] using hdk
  rcases path_indices (by omega : 2 < n) π a b c d hac hbd hab hbc hcd with h | h
  · exact forward a b c d h.1 h.2.1 h.2.2
  · obtain ⟨j, k, hj, hk, hjd, hak⟩ := forward d c b a h.1 h.2.1 h.2.2
    exact ⟨k, j, ⟨hk.2.2.2, hk.2.2.1, hk.2.1, hk.1⟩,
      ⟨hj.2.2.2, hj.2.2.1, hj.2.1, hj.1⟩, adj_symm hak, adj_symm hjd⟩

end CircletTSP.Facet.PathExtension

namespace CircletTSP.Facet.MinimalProof

open PathExtension

lemma adj_hasEdge {n : ℕ} {π : Equiv.Perm (Fin n)} {u v : Fin n} (h : Adj π u v) :
    HasEdge π (u.val + 1) (v.val + 1) := ⟨u, v, rfl, rfl, h⟩

lemma normalized_structure_chain (n : ℕ) (hn : 8 ≤ n) (π : Equiv.Perm (Fin n))
    (hstruct : IsStructA π ⟨0, by omega⟩ ∨ IsStructB2 π ⟨0, by omega⟩) :
    ∃ j k : ℕ, j ∈ keptLabels n ∧ k ∈ keptLabels n ∧ (ChainOne π j k ∨ ChainTwo π j k) := by
  let z : Fin n := ⟨0, by omega⟩
  let b : Fin n := shift z 1
  let c : Fin n := shift z (n / 2)
  let d : Fin n := shift z (1 + n / 2)
  have hz : z.val = 0 := rfl
  have hb : b.val = 1 := by simp [b, z, shift, Nat.mod_eq_of_lt (show 1 < n by omega)]
  have hc : c.val = n / 2 := by simp [c, z, shift, Nat.mod_eq_of_lt (show n / 2 < n by omega)]
  have hd : d.val = 1 + n / 2 := by
    simp [d, z, shift, Nat.mod_eq_of_lt (show 1 + n / 2 < n by omega)]
  have hzl : z.val + 1 = 1 := by omega
  have hbl : b.val + 1 = 2 := by omega
  have hcl : c.val + 1 = n / 2 + 1 := by omega
  have hdl : d.val + 1 = n / 2 + 2 := by omega
  have mem_kept (v : Fin n) (hvz : v ≠ z) (hvb : v ≠ b) (hvc : v ≠ c) (hvd : v ≠ d) :
      v.val + 1 ∈ keptLabels n := by
    have hv := v.isLt
    have hv0 : v.val ≠ 0 := fun h => hvz (Fin.ext (h.trans hz.symm))
    have hv1 : v.val ≠ 1 := fun h => hvb (Fin.ext (h.trans hb.symm))
    have hvd₀ : v.val ≠ n / 2 := fun h => hvc (Fin.ext (h.trans hc.symm))
    have hvd1 : v.val ≠ 1 + n / 2 := fun h => hvd (Fin.ext (h.trans hd.symm))
    simp only [keptLabels, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  have hac : z ≠ d := by intro h; have := congrArg Fin.val h; rw [hz, hd] at this; omega
  have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; rw [hb, hc] at this; omega
  rcases hstruct with h | h
  · change Adj π c z ∧ Adj π z b ∧ Adj π b d at h
    obtain ⟨j, k, hj, hk, hjd, hck⟩ := four_path_extend (by omega : 4 < n) π d b z c
      hac.symm hbc (adj_symm h.2.2) (adj_symm h.2.1) (adj_symm h.1)
    refine ⟨j.val + 1, k.val + 1, mem_kept j hj.2.2.1 hj.2.1 hj.2.2.2 hj.1,
      mem_kept k hk.2.2.1 hk.2.1 hk.2.2.2 hk.1, Or.inr ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hdl] using adj_hasEdge hjd
    · simpa only [hbl, hdl] using adj_hasEdge (adj_symm h.2.2)
    · simpa only [hbl, hzl] using adj_hasEdge (adj_symm h.2.1)
    · simpa only [hzl, hcl] using adj_hasEdge (adj_symm h.1)
    · simpa only [hcl] using adj_hasEdge hck
  · change Adj π z b ∧ Adj π b d ∧ Adj π d c at h
    obtain ⟨j, k, hj, hk, hjz, hck⟩ := four_path_extend (by omega : 4 < n) π z b d c
      hac hbc h.1 h.2.1 h.2.2
    refine ⟨j.val + 1, k.val + 1, mem_kept j hj.1 hj.2.1 hj.2.2.2 hj.2.2.1,
      mem_kept k hk.1 hk.2.1 hk.2.2.2 hk.2.2.1, Or.inl ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hzl] using adj_hasEdge hjz
    · simpa only [hzl, hbl] using adj_hasEdge h.1
    · simpa only [hbl, hdl] using adj_hasEdge h.2.1
    · simpa only [hdl, hcl] using adj_hasEdge h.2.2
    · simpa only [hcl] using adj_hasEdge hck

lemma no_normalized_structure (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n))
    (hlt : circletForm n (MetricTSP.tourVec π) < (n : ℝ) - 2)
    (hmin : ∀ m : ℕ, 0 < m → m < n → 4 ∣ m → ∀ σ : Equiv.Perm (Fin m),
      (m : ℝ) - 2 ≤ circletForm m (MetricTSP.tourVec σ)) :
    ¬ (IsStructA π ⟨0, by omega⟩ ∨ IsStructB2 π ⟨0, by omega⟩) := by
  intro h
  obtain ⟨j, k, hj, hk, hchain⟩ := normalized_structure_chain n hn π h
  obtain ⟨⟨σ, hσ⟩, hcost⟩ := contraction_step n hn h4 π j k hj hk hchain
  have hsmall := hmin (n - 4) (by omega) (by omega) (by omega) σ
  rw [hσ] at hsmall
  have hn4 : (4 : ℕ) ≤ n := by omega
  rw [Nat.cast_sub hn4] at hsmall
  norm_num at hsmall
  linarith

lemma minimal_no_structures (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n))
    (hlt : circletForm n (MetricTSP.tourVec π) < (n : ℝ) - 2)
    (hmin : ∀ m : ℕ, 0 < m → m < n → 4 ∣ m → ∀ σ : Equiv.Perm (Fin m),
      (m : ℝ) - 2 ≤ circletForm m (MetricTSP.tourVec σ)) :
    ∀ u : Fin n, ¬ IsStructA π u ∧ ¬ IsStructB1 π u ∧ ¬ IsStructB2 π u := by
  have hn8 : 8 ≤ n := by
    by_cases hbase : n = 4
    · subst n
      have h := Base4.base_case π
      norm_num at h hlt
      linarith
    · omega
  have noAorB₂ (ρ : Equiv.Perm (Fin n))
      (hρ : circletForm n (MetricTSP.tourVec ρ) < (n : ℝ) - 2) (u : Fin n) :
      ¬ IsStructA ρ u ∧ ¬ IsStructB2 ρ u := by
    constructor
    · intro h
      obtain ⟨ρ', heq, hzero⟩ := (claim_4_2 n hn h4 ρ u).1 h
      apply no_normalized_structure n hn8 h4 ρ' (by linarith) hmin
      exact Or.inl hzero
    · intro h
      obtain ⟨ρ', heq, hzero⟩ := (claim_4_2 n hn h4 ρ u).2 h
      apply no_normalized_structure n hn8 h4 ρ' (by linarith) hmin
      exact Or.inr hzero
  intro u
  refine ⟨(noAorB₂ π hlt u).1, ?_, (noAorB₂ π hlt u).2⟩
  intro h
  obtain ⟨ρ, v, heq, hB₂⟩ := (claim_4_1 n hn h4).2 π u h
  exact (noAorB₂ ρ (by linarith) v).2 hB₂

end CircletTSP.Facet.MinimalProof

namespace CircletTSP.Facet.C5

lemma half_window_count (n : ℕ) (hn : 0 < n) :
    (Finset.univ.filter (fun u : Fin n => u.val < n / 2)).card = n / 2 := by
  let d : Fin n := ⟨n / 2, Nat.div_lt_self hn (by decide)⟩
  have heq : Finset.univ.filter (fun u : Fin n => u.val < n / 2) = Finset.Iio d := by
    ext u
    simp [Fin.lt_def, d]
  rw [heq, Fin.card_Iio]

lemma window_sum_le_n (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n))
    (hw : ∀ u : Fin n, window π u ≤ 2) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin n => u.val < n / 2), window π u) ≤ n := by
  calc
    _ ≤ ∑ _u ∈ Finset.univ.filter (fun u : Fin n => u.val < n / 2), (2 : ℝ) :=
      Finset.sum_le_sum fun u _ => hw u
    _ = ((n / 2 : ℕ) : ℝ) * 2 := by simp [half_window_count n hn]
    _ = (n : ℝ) := by
      have h2 : 2 ∣ n := dvd_trans (by decide : 2 ∣ 4) h4
      exact_mod_cast Nat.div_mul_cancel h2

end CircletTSP.Facet.C5

open CircletTSP.Facet

/-- Strong induction implements the paper's minimal-counterexample argument. -/
theorem solution (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n)) :
    (n : ℝ) - 2 ≤ circletForm n (MetricTSP.tourVec π) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hbase : n = 4
    · subst n
      exact Base4.base_case π
    have hn8 : 8 ≤ n := by omega
    by_contra hnot
    have hlt : circletForm n (MetricTSP.tourVec π) < (n : ℝ) - 2 := lt_of_not_ge hnot
    have hmin : ∀ m : ℕ, 0 < m → m < n → 4 ∣ m → ∀ σ : Equiv.Perm (Fin m),
        (m : ℝ) - 2 ≤ circletForm m (MetricTSP.tourVec σ) := by
      intro m hm hmn hm4 σ
      exact ih m hmn hm hm4 σ
    have hno := MinimalProof.minimal_no_structures n hn h4 π hlt hmin
    have hw := WindowBoundProof.window_le_two_direct n hn8 h4 π hno
    have hsum := C5.window_sum_le_n n hn h4 π hw
    have hcount := window_count n hn h4 π
    have hdense := Counterbound.counterbound n hn h4 π hlt
    linarith
