-- Prove2me | solution 1 for CircletTSP.Facet.contraction_step
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:35:38.78101+00:00
-- url     : https://prove2.me/submissions/10181769-50d9-4fcb-9949-240628f5c272

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



set_option autoImplicit false

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


end CircletTSP.Facet.WindowBoundProof


set_option autoImplicit false

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


set_option autoImplicit false

namespace CircletTSP.Facet.ChainOrientation

open Fin.NatCast PathExtension

lemma forward_endpoints {n : ℕ} [NeZero n] (hn : 2 < n) (π : Equiv.Perm (Fin n))
    (j a b c d k : Fin n) (hjb : j ≠ b) (hkc : k ≠ c)
    (hja : Adj π j a) (hdk : Adj π d k)
    (hb : π.symm b = π.symm a + 1) (hc : π.symm c = π.symm a + 2)
    (hd : π.symm d = π.symm a + 3) :
    π.symm j = π.symm a - 1 ∧ π.symm k = π.symm a + 4 := by
  constructor
  · rcases (adj_iff_indices hn π j a).mp hja with h | h
    · calc
        π.symm j = (π.symm j + 1) - 1 := by abel
        _ = π.symm a - 1 := by rw [← h]
    · exact (hjb (π.symm.injective (h.trans hb.symm))).elim
  · rcases (adj_iff_indices hn π d k).mp hdk with h | h
    · rw [h, hd]
      norm_num [add_assoc]
    · have hdc : π.symm d = π.symm c + 1 := by rw [hd, hc]; norm_num [add_assoc]
      have hkc' : π.symm k = π.symm c := add_right_cancel (h.symm.trans hdc)
      exact (hkc (π.symm.injective hkc')).elim

lemma endpoint_ne {n : ℕ} [NeZero n] (hn : 5 < n) (π : Equiv.Perm (Fin n))
    (j k i : Fin n) (hj : π.symm j = i - 1) (hk : π.symm k = i + 4) : j ≠ k := by
  intro h
  have heq : i - 1 = i + 4 := hj.symm.trans ((congrArg π.symm h).trans hk)
  have heq' : i + (0 : Fin n) = i + (5 : Fin n) := by
    calc
      _ = (i - 1) + 1 := by abel
      _ = (i + 4) + 1 := by rw [heq]
      _ = _ := by norm_num [add_assoc]
  have hbad := offset_injective (a := 0) (b := 5) i (by omega) hn heq'
  omega

lemma five_chain_indices {n : ℕ} [NeZero n] (hn : 8 ≤ n) (π : Equiv.Perm (Fin n))
    (j a b c d k : Fin n) (hac : a ≠ c) (hbd : b ≠ d)
    (hjb : j ≠ b) (hkc : k ≠ c)
    (hja : Adj π j a) (hab : Adj π a b) (hbc : Adj π b c)
    (hcd : Adj π c d) (hdk : Adj π d k) :
    j ≠ k ∧
      ((π.symm j = π.symm a - 1 ∧ π.symm b = π.symm a + 1 ∧
        π.symm c = π.symm a + 2 ∧ π.symm d = π.symm a + 3 ∧
        π.symm k = π.symm a + 4) ∨
       (π.symm k = π.symm d - 1 ∧ π.symm c = π.symm d + 1 ∧
        π.symm b = π.symm d + 2 ∧ π.symm a = π.symm d + 3 ∧
        π.symm j = π.symm d + 4)) := by
  rcases path_indices (by omega : 2 < n) π a b c d hac hbd hab hbc hcd with h | h
  · obtain ⟨hj, hk⟩ := forward_endpoints (by omega : 2 < n) π j a b c d k hjb hkc hja hdk
      h.1 h.2.1 h.2.2
    exact ⟨endpoint_ne (by omega) π j k (π.symm a) hj hk,
      Or.inl ⟨hj, h.1, h.2.1, h.2.2, hk⟩⟩
  · obtain ⟨hk, hj⟩ := forward_endpoints (by omega : 2 < n) π k d c b a j hkc hjb
      (adj_symm hdk) (adj_symm hja) h.1 h.2.1 h.2.2
    exact ⟨(endpoint_ne (by omega) π k j (π.symm d) hk hj).symm,
      Or.inr ⟨hk, h.1, h.2.1, h.2.2, hj⟩⟩

end CircletTSP.Facet.ChainOrientation

namespace CircletTSP.Facet.ContractTour

lemma kept_iff (n s : ℕ) : s ∈ keptLabels n ↔
    1 ≤ s ∧ s ≤ n ∧ s ≠ 1 ∧ s ≠ 2 ∧ s ≠ n / 2 + 1 ∧ s ≠ n / 2 + 2 := by
  simp [keptLabels, and_assoc]

lemma unrelabel_kept (n : ℕ) (hn : 8 ≤ n) (w : Fin (n - 4)) :
    (unrelabel n w).val + 1 ∈ keptLabels n := by
  rw [kept_iff]
  have hw := w.isLt
  dsimp [unrelabel]
  split_ifs <;> omega

def lower (n : ℕ) (hn : 8 ≤ n) (v : Fin n)
    (hv : v.val + 1 ∈ keptLabels n) : Fin (n - 4) :=
  ⟨relabel n (v.val + 1) - 1, by
    rw [kept_iff] at hv
    dsimp [relabel]
    split_ifs <;> omega⟩

lemma unrelabel_lower (n : ℕ) (hn : 8 ≤ n) (v : Fin n)
    (hv : v.val + 1 ∈ keptLabels n) : unrelabel n (lower n hn v hv) = v := by
  apply Fin.ext
  rw [kept_iff] at hv
  dsimp [unrelabel, lower, relabel]
  split_ifs <;> omega

lemma lower_label (n : ℕ) (hn : 8 ≤ n) (v : Fin n)
    (hv : v.val + 1 ∈ keptLabels n) :
    (lower n hn v hv).val + 1 = relabel n (v.val + 1) := by
  have hv' := (kept_iff n _).mp hv
  dsimp [lower, relabel]
  split_ifs <;> omega

lemma unrelabel_injective (n : ℕ) (_hn : 8 ≤ n) : Function.Injective (unrelabel n) := by
  intro u v h
  apply Fin.ext
  have h' := congrArg Fin.val h
  dsimp [unrelabel] at h'
  split_ifs at h' <;> omega

lemma lower_unrelabel (n : ℕ) (hn : 8 ≤ n) (w : Fin (n - 4)) :
    lower n hn (unrelabel n w) (unrelabel_kept n hn w) = w := by
  apply unrelabel_injective n hn
  exact unrelabel_lower n hn _ _

def skip (n : ℕ) (hn : 8 ≤ n) (p : Fin (n - 4)) : Fin n :=
  ⟨if p.val = 0 then 0 else p.val + 4, by have := p.isLt; split_ifs <;> omega⟩

lemma skip_injective (n : ℕ) (hn : 8 ≤ n) : Function.Injective (skip n hn) := by
  intro p q h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [skip] at hv
  split_ifs at hv <;> omega

lemma skip_not_removed (n : ℕ) (hn : 8 ≤ n) (p : Fin (n - 4)) :
    ¬ (1 ≤ (skip n hn p).val ∧ (skip n hn p).val ≤ 4) := by
  dsimp [skip]
  split_ifs <;> omega

def shortIndex (n : ℕ) (hn : 8 ≤ n) (ρ : Equiv.Perm (Fin n))
    (hkeep : ∀ p : Fin n, (ρ p).val + 1 ∈ keptLabels n ↔ ¬ (1 ≤ p.val ∧ p.val ≤ 4))
    (p : Fin (n - 4)) : Fin (n - 4) :=
  lower n hn (ρ (skip n hn p)) ((hkeep _).mpr (skip_not_removed n hn p))

lemma shortIndex_lift (n : ℕ) (hn : 8 ≤ n) (ρ : Equiv.Perm (Fin n))
    (hkeep : ∀ p : Fin n, (ρ p).val + 1 ∈ keptLabels n ↔ ¬ (1 ≤ p.val ∧ p.val ≤ 4))
    (p : Fin (n - 4)) : unrelabel n (shortIndex n hn ρ hkeep p) = ρ (skip n hn p) :=
  unrelabel_lower n hn _ _

lemma shortIndex_injective (n : ℕ) (hn : 8 ≤ n) (ρ : Equiv.Perm (Fin n))
    (hkeep : ∀ p : Fin n, (ρ p).val + 1 ∈ keptLabels n ↔ ¬ (1 ≤ p.val ∧ p.val ≤ 4)) :
    Function.Injective (shortIndex n hn ρ hkeep) := by
  intro p q h
  apply skip_injective n hn
  apply ρ.injective
  simpa only [shortIndex_lift] using congrArg (unrelabel n) h

noncomputable def shortTour (n : ℕ) (hn : 8 ≤ n) (ρ : Equiv.Perm (Fin n))
    (hkeep : ∀ p : Fin n, (ρ p).val + 1 ∈ keptLabels n ↔ ¬ (1 ≤ p.val ∧ p.val ≤ 4)) :
    Equiv.Perm (Fin (n - 4)) :=
  Equiv.ofBijective (shortIndex n hn ρ hkeep)
    ⟨shortIndex_injective n hn ρ hkeep,
      Finite.surjective_of_injective (shortIndex_injective n hn ρ hkeep)⟩

lemma shortTour_lift (n : ℕ) (hn : 8 ≤ n) (ρ : Equiv.Perm (Fin n))
    (hkeep : ∀ p : Fin n, (ρ p).val + 1 ∈ keptLabels n ↔ ¬ (1 ≤ p.val ∧ p.val ≤ 4))
    (p : Fin (n - 4)) : unrelabel n (shortTour n hn ρ hkeep p) = ρ (skip n hn p) :=
  shortIndex_lift n hn ρ hkeep p

lemma rotate_val {n : ℕ} (p : Fin n) :
    (finRotate n p).val = if p.val + 1 < n then p.val + 1 else 0 := by
  cases n with
  | zero => exact Fin.elim0 p
  | succ m =>
    rw [coe_finRotate]
    by_cases hp : p = Fin.last m
    · subst p; simp
    · have hlt := Fin.val_lt_last hp
      simp [hp, show p.val + 1 < m + 1 by omega]

lemma tourVec_at_positions {n : ℕ} (hn : 1 < n) (ρ : Equiv.Perm (Fin n)) (p q : Fin n) :
    MetricTSP.tourVec ρ (ρ p) (ρ q) =
      (if finRotate n p = q then 1 else 0) + (if finRotate n q = p then 1 else 0) := by
  simp only [TourCounts.tourVec_eq_successors_all hn, TourCounts.successorPerm,
    Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq]

lemma skip_successor_iff (n : ℕ) (hn : 8 ≤ n) (p q : Fin (n - 4)) :
    finRotate n (skip n hn p) = skip n hn q ↔
      finRotate (n - 4) p = q ∧ ¬ (p.val = 0 ∧ q.val = 1) := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [Fin.ext_iff, rotate_val]
  change (if (if p.val = 0 then 0 else p.val + 4) + 1 < n
    then (if p.val = 0 then 0 else p.val + 4) + 1 else 0) =
      (if q.val = 0 then 0 else q.val + 4) ↔
    (if p.val + 1 < n - 4 then p.val + 1 else 0) = q.val ∧
      ¬ (p.val = 0 ∧ q.val = 1)
  split_ifs <;> simp_all <;> omega

lemma short_successor_indicator (n : ℕ) (hn : 8 ≤ n) (p q : Fin (n - 4)) :
    (if finRotate (n - 4) p = q then (1 : ℝ) else 0) =
      (if finRotate n (skip n hn p) = skip n hn q then 1 else 0) +
      (if p.val = 0 ∧ q.val = 1 then 1 else 0) := by
  simp only [skip_successor_iff]
  by_cases he : p.val = 0 ∧ q.val = 1
  · have hr : finRotate (n - 4) p = q := by
      apply Fin.ext
      rw [rotate_val, he.1, if_pos (by omega)]
      omega
    simp [he, hr]
  · simp [he]

lemma skip_edge_formula (n : ℕ) (hn : 8 ≤ n) (p q : Fin (n - 4)) :
    ((if finRotate (n - 4) p = q then 1 else 0) +
      (if finRotate (n - 4) q = p then 1 else 0) : ℝ) =
    ((if finRotate n (skip n hn p) = skip n hn q then 1 else 0) +
      (if finRotate n (skip n hn q) = skip n hn p then 1 else 0)) +
    (if (p.val = 0 ∧ q.val = 1) ∨ (p.val = 1 ∧ q.val = 0) then 1 else 0) := by
  rw [short_successor_indicator n hn p q, short_successor_indicator n hn q p]
  by_cases hpq : p.val = 0 ∧ q.val = 1
  · have hqp : ¬ (q.val = 0 ∧ p.val = 1) := by omega
    simp [hpq]
    ring
  · by_cases hqp : q.val = 0 ∧ p.val = 1
    · have hqp' : p.val = 1 ∧ q.val = 0 := hqp.symm
      simp [hqp]
      ring
    · have hqp' : ¬ (p.val = 1 ∧ q.val = 0) := by omega
      simp only [hpq, hqp, hqp', false_or, if_false]
      ring

lemma label_eq_iff {m : ℕ} (σ : Equiv.Perm (Fin m)) (p q : Fin m) :
    (σ p).val + 1 = (σ q).val + 1 ↔ p = q := by
  constructor
  · intro h
    exact σ.injective (Fin.ext (Nat.add_right_cancel h))
  · rintro rfl
    rfl

lemma shortTour_vector (n : ℕ) (hn : 8 ≤ n) (ρ : Equiv.Perm (Fin n))
    (hkeep : ∀ p : Fin n, (ρ p).val + 1 ∈ keptLabels n ↔ ¬ (1 ≤ p.val ∧ p.val ≤ 4)) :
    MetricTSP.tourVec (shortTour n hn ρ hkeep) =
      contract n (MetricTSP.tourVec ρ) ((ρ ⟨0, by omega⟩).val + 1)
        ((ρ ⟨5, by omega⟩).val + 1) := by
  let σ := shortTour n hn ρ hkeep
  let p₀ : Fin (n - 4) := ⟨0, by omega⟩
  let p₁ : Fin (n - 4) := ⟨1, by omega⟩
  have hlabel (p : Fin (n - 4)) :
      (σ p).val + 1 = relabel n ((ρ (skip n hn p)).val + 1) :=
    lower_label n hn _ ((hkeep _).mpr (skip_not_removed n hn p))
  have hlabel₀ : (σ p₀).val + 1 = relabel n ((ρ ⟨0, by omega⟩).val + 1) := by
    simpa only [skip, p₀, ↓reduceIte] using hlabel p₀
  have hlabel₁ : (σ p₁).val + 1 = relabel n ((ρ ⟨5, by omega⟩).val + 1) := by
    simpa [skip, p₁] using hlabel p₁
  funext a b
  obtain ⟨p, rfl⟩ := σ.surjective a
  obtain ⟨q, rfl⟩ := σ.surjective b
  change MetricTSP.tourVec σ (σ p) (σ q) = _
  simp only [contract]
  rw [show unrelabel n (σ p) = ρ (skip n hn p) from shortTour_lift n hn ρ hkeep p,
    show unrelabel n (σ q) = ρ (skip n hn q) from shortTour_lift n hn ρ hkeep q]
  rw [tourVec_at_positions (by omega), tourVec_at_positions (by omega)]
  rw [skip_edge_formula n hn p q]
  rw [← hlabel₀, ← hlabel₁]
  simp only [label_eq_iff, Fin.ext_iff, p₀, p₁]

open Fin.NatCast in
noncomputable def positionRotate {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n))
    (s : Fin n) : Equiv.Perm (Fin n) := (Equiv.addLeft s).trans π

open Fin.NatCast in
lemma positionRotate_apply {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n))
    (s p : Fin n) : positionRotate π s p = π (s + p) := rfl

lemma positionRotate_vector {n : ℕ} [NeZero n] (hn : 1 < n) (π : Equiv.Perm (Fin n))
    (s : Fin n) : MetricTSP.tourVec (positionRotate π s) = MetricTSP.tourVec π := by
  funext a b
  obtain ⟨p, rfl⟩ := (positionRotate π s).surjective a
  obtain ⟨q, rfl⟩ := (positionRotate π s).surjective b
  rw [tourVec_at_positions hn]
  simp only [positionRotate_apply]
  rw [tourVec_at_positions hn]
  simp only [finRotate_apply, add_assoc, add_left_cancel_iff]

open Fin.NatCast in
lemma forward_contract {n : ℕ} [NeZero n] (hn : 8 ≤ n) (π : Equiv.Perm (Fin n))
    (j a b c d k : Fin n)
    (hbad : ∀ v : Fin n, v.val + 1 ∉ keptLabels n ↔ v = a ∨ v = b ∨ v = c ∨ v = d)
    (hj : π.symm j = π.symm a - 1) (hb : π.symm b = π.symm a + 1)
    (hc : π.symm c = π.symm a + 2) (hd : π.symm d = π.symm a + 3)
    (hk : π.symm k = π.symm a + 4) :
    ∃ σ : Equiv.Perm (Fin (n - 4)),
      MetricTSP.tourVec σ = contract n (MetricTSP.tourVec π) (j.val + 1) (k.val + 1) := by
  let ρ := positionRotate π (π.symm a - 1)
  have hρ₀ : ρ 0 = j := by
    apply π.symm.injective
    simpa [ρ, positionRotate_apply] using hj.symm
  have hρ₁ : ρ 1 = a := by simp [ρ, positionRotate_apply]
  have hρ₂ : ρ 2 = b := by
    apply π.symm.injective
    simp only [ρ, positionRotate_apply, Equiv.symm_apply_apply, hb]
    rw [show (2 : Fin n) = 1 + 1 by norm_num]
    abel
  have hρ₃ : ρ 3 = c := by
    apply π.symm.injective
    simp only [ρ, positionRotate_apply, Equiv.symm_apply_apply, hc]
    rw [show (3 : Fin n) = 1 + 2 by norm_num]
    abel
  have hρ₄ : ρ 4 = d := by
    apply π.symm.injective
    simp only [ρ, positionRotate_apply, Equiv.symm_apply_apply, hd]
    rw [show (4 : Fin n) = 1 + 3 by norm_num]
    abel
  have hρ₅ : ρ 5 = k := by
    apply π.symm.injective
    simp only [ρ, positionRotate_apply, Equiv.symm_apply_apply, hk]
    rw [show (5 : Fin n) = 1 + 4 by norm_num]
    abel
  have h1 : (1 : Fin n).val = 1 := by change 1 % n = 1; exact Nat.mod_eq_of_lt (by omega)
  have h2 : (2 : Fin n).val = 2 := by change 2 % n = 2; exact Nat.mod_eq_of_lt (by omega)
  have h3 : (3 : Fin n).val = 3 := by change 3 % n = 3; exact Nat.mod_eq_of_lt (by omega)
  have h4 : (4 : Fin n).val = 4 := by change 4 % n = 4; exact Nat.mod_eq_of_lt (by omega)
  have hkeep (p : Fin n) : (ρ p).val + 1 ∈ keptLabels n ↔ ¬ (1 ≤ p.val ∧ p.val ≤ 4) := by
    have hpbad := hbad (ρ p)
    rw [← hρ₁, ← hρ₂, ← hρ₃, ← hρ₄] at hpbad
    simp only [Equiv.apply_eq_iff_eq, Fin.ext_iff, h1, h2, h3, h4] at hpbad
    have heq : (p.val = 1 ∨ p.val = 2 ∨ p.val = 3 ∨ p.val = 4) ↔
        (1 ≤ p.val ∧ p.val ≤ 4) := by omega
    have hnot := hpbad.trans heq
    simpa only [not_not] using not_congr hnot
  refine ⟨shortTour n hn ρ hkeep, ?_⟩
  have hzero : (⟨0, by omega⟩ : Fin n) = 0 := by apply Fin.ext; simp
  have hfive : (⟨5, by omega⟩ : Fin n) = 5 := by apply Fin.ext; simp [Nat.mod_eq_of_lt (show 5 < n by omega)]
  rw [shortTour_vector n hn ρ hkeep, hzero, hfive, hρ₀, hρ₅]
  rw [positionRotate_vector (by omega)]

lemma contract_symm (n : ℕ) (x : Fin n → Fin n → ℝ) (j k : ℕ) :
    contract n x j k = contract n x k j := by
  funext a b
  simp only [contract, or_comm]

lemma contract_from_chain {n : ℕ} [NeZero n] (hn : 8 ≤ n) (π : Equiv.Perm (Fin n))
    (j a b c d k : Fin n)
    (hbad : ∀ v : Fin n, v.val + 1 ∉ keptLabels n ↔ v = a ∨ v = b ∨ v = c ∨ v = d)
    (hac : a ≠ c) (hbd : b ≠ d) (hjb : j ≠ b) (hkc : k ≠ c)
    (hja : Adj π j a) (hab : Adj π a b) (hbc : Adj π b c)
    (hcd : Adj π c d) (hdk : Adj π d k) :
    (∃ σ : Equiv.Perm (Fin (n - 4)),
      MetricTSP.tourVec σ = contract n (MetricTSP.tourVec π) (j.val + 1) (k.val + 1)) ∧ j ≠ k := by
  obtain ⟨hjk, hf | hr⟩ := ChainOrientation.five_chain_indices hn π j a b c d k
    hac hbd hjb hkc hja hab hbc hcd hdk
  · exact ⟨forward_contract hn π j a b c d k hbad hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2, hjk⟩
  · have hbad' (v : Fin n) : v.val + 1 ∉ keptLabels n ↔ v = d ∨ v = c ∨ v = b ∨ v = a := by
      rw [hbad]
      tauto
    obtain ⟨σ, hσ⟩ := forward_contract hn π k d c b a j hbad'
      hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2
    exact ⟨⟨σ, hσ.trans (contract_symm n _ _ _)⟩, hjk⟩

lemma hasEdge_to_adj {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) (a b : ℕ)
    (hu : u.val + 1 = a) (hv : v.val + 1 = b) (h : HasEdge π a b) : Adj π u v := by
  obtain ⟨u', v', hu', hv', he⟩ := h
  have eu : u' = u := Fin.ext (by omega)
  have ev : v' = v := Fin.ext (by omega)
  simpa only [Adj, eu, ev] using he

lemma contract_tour (n : ℕ) (hn : 8 ≤ n) (_h4 : 4 ∣ n) (π : Equiv.Perm (Fin n)) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hchain : ChainOne π j k ∨ ChainTwo π j k) :
    (∃ σ : Equiv.Perm (Fin (n - 4)),
      MetricTSP.tourVec σ = contract n (MetricTSP.tourVec π) j k) ∧ j ≠ k := by
  clear _h4
  let : NeZero n := ⟨by omega⟩
  have hj' := (kept_iff n j).mp hj
  have hk' := (kept_iff n k).mp hk
  let J : Fin n := ⟨j - 1, by omega⟩
  let K : Fin n := ⟨k - 1, by omega⟩
  let A : Fin n := ⟨0, by omega⟩
  let B : Fin n := ⟨1, by omega⟩
  let C : Fin n := ⟨n / 2 + 1, by omega⟩
  let D : Fin n := ⟨n / 2, by omega⟩
  have hJ : J.val + 1 = j := by dsimp [J]; omega
  have hK : K.val + 1 = k := by dsimp [K]; omega
  have hbad (v : Fin n) : v.val + 1 ∉ keptLabels n ↔ v = A ∨ v = B ∨ v = C ∨ v = D := by
    rw [kept_iff]
    simp only [Fin.ext_iff]
    dsimp [A, B, C, D]
    have hv := v.isLt
    omega
  have hres : (∃ σ : Equiv.Perm (Fin (n - 4)),
      MetricTSP.tourVec σ = contract n (MetricTSP.tourVec π) (J.val + 1) (K.val + 1)) ∧ J ≠ K := by
    rcases hchain with h | h
    · obtain ⟨hja, hab, hbc, hcd, hdk⟩ := h
      apply contract_from_chain hn π J A B C D K hbad
      · intro he; have := congrArg Fin.val he; dsimp [A, C] at this; omega
      · intro he; have := congrArg Fin.val he; dsimp [B, D] at this; omega
      · intro he; have := congrArg Fin.val he; dsimp [J, B] at this; omega
      · intro he; have := congrArg Fin.val he; dsimp [K, C] at this; omega
      · exact hasEdge_to_adj π J A j 1 hJ rfl hja
      · exact hasEdge_to_adj π A B 1 2 rfl rfl hab
      · exact hasEdge_to_adj π B C 2 (n / 2 + 2) rfl rfl hbc
      · exact hasEdge_to_adj π C D (n / 2 + 2) (n / 2 + 1) rfl rfl hcd
      · exact hasEdge_to_adj π D K (n / 2 + 1) k rfl hK hdk
    · obtain ⟨hja, hab, hbc, hcd, hdk⟩ := h
      have hbad' (v : Fin n) : v.val + 1 ∉ keptLabels n ↔ v = C ∨ v = B ∨ v = A ∨ v = D := by
        rw [hbad]
        tauto
      apply contract_from_chain hn π J C B A D K hbad'
      · intro he; have := congrArg Fin.val he; dsimp [A, C] at this; omega
      · intro he; have := congrArg Fin.val he; dsimp [B, D] at this; omega
      · intro he; have := congrArg Fin.val he; dsimp [J, B] at this; omega
      · intro he; have := congrArg Fin.val he; dsimp [K, A] at this; omega
      · exact hasEdge_to_adj π J C j (n / 2 + 2) hJ rfl hja
      · exact hasEdge_to_adj π C B (n / 2 + 2) 2 rfl rfl hab
      · exact hasEdge_to_adj π B A 2 1 rfl rfl hbc
      · exact hasEdge_to_adj π A D 1 (n / 2 + 1) rfl rfl hcd
      · exact hasEdge_to_adj π D K (n / 2 + 1) k rfl hK hdk
  constructor
  · simpa only [hJ, hK] using hres.1
  · intro he
    apply hres.2
    apply Fin.ext
    omega

end CircletTSP.Facet.ContractTour

namespace CircletTSP.Facet.TightProof

noncomputable section

theorem cycLen_symm {n : ℕ} (u v : Fin n) : cycLen n u v = cycLen n v u := by
  have h : (u.val : ℤ) - v.val = -((v.val : ℤ) - u.val) := by omega
  simp only [cycLen, h, Int.natAbs_neg]

theorem circletForm_eq_weighted_edges (n : ℕ) (x : Fin n → Fin n → ℝ) :
    circletForm n x = ∑ u : Fin n, ∑ v : Fin n,
      if u < v then (coeff n (cycLen n u v) : ℝ) * x u v else 0 := by
  unfold circletForm lenCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : u < v
  · have hmem := TourCounts.cycLen_mem_range_of_lt u v huv
    simp [huv, hmem, eq_comm]
  · simp [huv]

private theorem single_edge_weight_of_lt {n : ℕ} (w : Fin n → Fin n → ℝ)
    (a b : Fin n) (hab : a < b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then w u v else 0) = w a b := by
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

private theorem single_edge_weight {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hw : ∀ u v, w u v = w v u) (a b : Fin n) (hab : a ≠ b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then w u v else 0) = w a b := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact single_edge_weight_of_lt w a b h
  · simpa [or_comm, and_comm, hw b a] using single_edge_weight_of_lt w b a h

theorem weighted_tour_eq_step_sum {n : ℕ} (hn : 1 < n)
    (w : Fin n → Fin n → ℝ) (hw : ∀ u v, w u v = w v u)
    (π : Equiv.Perm (Fin n)) :
    (∑ u : Fin n, ∑ v : Fin n, if u < v then w u v * MetricTSP.tourVec π u v else 0) =
      ∑ k : Fin n, w (π k) (π (finRotate n k)) := by
  have hexpand (u v : Fin n) :
      (if u < v then w u v * MetricTSP.tourVec π u v else 0) =
      ∑ k : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then w u v else 0 := by
    rw [TourCounts.tourVec_eq_step_sum]
    by_cases huv : u < v
    · simp only [huv, if_true, true_and, Finset.mul_sum, mul_ite, mul_one, mul_zero]
    · simp only [huv, if_false, false_and, Finset.sum_const_zero]
  simp_rw [hexpand]
  calc
    _ = ∑ u : Fin n, ∑ k : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then w u v else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ u : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then w u v else 0 := by rw [Finset.sum_comm]
    _ = ∑ k : Fin n, w (π k) (π (finRotate n k)) := by
      apply Finset.sum_congr rfl
      intro k _
      apply single_edge_weight w hw
      intro h
      exact TourCounts.rotate_ne_self hn k (π.injective h).symm

theorem circletForm_tour_eq_step_sum {n : ℕ} (hn : 1 < n)
    (π : Equiv.Perm (Fin n)) :
    circletForm n (MetricTSP.tourVec π) =
      ∑ k : Fin n, (coeff n (cycLen n (π k) (π (finRotate n k))) : ℝ) := by
  rw [circletForm_eq_weighted_edges]
  apply weighted_tour_eq_step_sum hn
  intro u v
  rw [cycLen_symm]

end

end CircletTSP.Facet.TightProof


namespace CircletTSP.Facet.ContractionReduction

noncomputable section

theorem cycLen_le_half {n : ℕ} (u v : Fin n) : cycLen n u v ≤ n/2 := by
  have hu := u.isLt
  have hv := v.isLt
  by_cases h : u.val ≤ v.val
  · simp only [cycLen,Int.natAbs_natCast_sub_natCast_of_le h]
    omega
  · have h' : v.val ≤ u.val := by omega
    simp only [cycLen,Int.natAbs_natCast_sub_natCast_of_ge h']
    omega

theorem labLen_eq_cycLen {n : ℕ} (u v : Fin n) :
    labLen n (u.val+1) (v.val+1) = (cycLen n u v : ℤ) := by
  have hu := u.isLt
  have hv := v.isLt
  have habs : ((u.val : ℤ)-v.val).natAbs ≤ n := by
    by_cases h : u.val ≤ v.val
    · rw [Int.natAbs_natCast_sub_natCast_of_le h]; omega
    · rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega : v.val ≤ u.val)]; omega
  simp only [labLen,cycLen,Nat.cast_add,Nat.cast_one,add_sub_add_right_eq_sub,
    Nat.cast_min,Nat.cast_sub habs,Int.natCast_natAbs]

theorem labCost_eq_coeff {n : ℕ} (u v : Fin n) :
    labCost n (u.val+1) (v.val+1) = (coeff n (cycLen n u v) : ℤ) := by
  rw [labCost,labLen_eq_cycLen]
  have hlen := cycLen_le_half u v
  have hpar : ((cycLen n u v : ℤ) % 2 = 1) ↔ cycLen n u v % 2 = 1 := by omega
  simp only [coeff,hpar]
  split_ifs <;> simp [Nat.cast_sub hlen]

theorem circletForm_eq_labCost_sum (n : ℕ) (x : Fin n → Fin n → ℝ) :
    circletForm n x = ∑ u, ∑ v,
      if u<v then (labCost n (u.val+1) (v.val+1) : ℝ)*x u v else 0 := by
  rw [TightProof.circletForm_eq_weighted_edges]
  simp only [labCost_eq_coeff,Int.cast_natCast]

theorem conCost_eq_labCost (n : ℕ) (hn : 4 ≤ n) (a b : ℕ) :
    conCost n a b = labCost (n-4) a b := by
  have hn4 : ((n-4:ℕ):ℤ) = (n:ℤ)-4 := by omega
  have hhalf : (((n-4)/2:ℕ):ℤ) = ((n/2:ℕ):ℤ)-2 := by omega
  simp only [conCost,conLen,labCost,labLen,hn4,hhalf]
  rfl

theorem circletForm_contracted_eq_cost_sum (n : ℕ) (hn : 4 ≤ n)
    (x : Fin (n-4) → Fin (n-4) → ℝ) :
    circletForm (n-4) x = ∑ a, ∑ b,
      if a<b then (conCost n (a.val+1) (b.val+1) : ℝ)*x a b else 0 := by
  rw [circletForm_eq_labCost_sum]
  simp only [conCost_eq_labCost n hn]

theorem labCost_symm (n a b : ℕ) : labCost n a b = labCost n b a := by
  simp only [labCost,labLen,abs_sub_comm (a:ℤ) b]
  rfl

theorem conCost_symm (n a b : ℕ) : conCost n a b = conCost n b a := by
  simp only [conCost,conLen,abs_sub_comm (a:ℤ) b]
  rfl

end
end CircletTSP.Facet.ContractionReduction


set_option autoImplicit false

namespace CircletTSP.Facet.ContractionReduction

theorem row_saturated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hnonneg : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 2)
    (a b : ι) (hab : a ≠ b) (ha : x a = 1) (hb : x b = 1)
    (c : ι) (hca : c ≠ a) (hcb : c ≠ b) : x c = 0 := by
  have hlower : (∑ i ∈ ({a, b, c} : Finset ι), x i) ≤ ∑ i, x i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hnonneg i)
  simp [hab, Ne.symm hca, Ne.symm hcb, ha, hb, hsum] at hlower
  have hc := hnonneg c
  linarith

theorem row_eq_two_indicators {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hnonneg : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 2)
    (a b : ι) (hab : a ≠ b) (ha : x a = 1) (hb : x b = 1)
    (c : ι) : x c = (if c = a then 1 else 0) + (if c = b then 1 else 0) := by
  by_cases hca : c = a
  · subst c; simp [ha, hab]
  by_cases hcb : c = b
  · subst c; simp [hb, hca]
  simp [hca, hcb, row_saturated x hnonneg hsum a b hab ha hb c hca hcb]

def edgeIndicator {ι : Type*} [DecidableEq ι] (p q u v : ι) : ℝ :=
  (if p = u ∧ q = v then 1 else 0) + (if q = u ∧ p = v then 1 else 0)

theorem matrix_chain_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ι → ℝ) (hsym : ∀ u v, X u v = X v u)
    (hnonneg : ∀ u v, 0 ≤ X u v) (hrow : ∀ u, ∑ v, X u v = 2)
    (j a b c d k : ι) (hnodes : Function.Injective (![j,a,b,c,d,k] : Fin 6 → ι))
    (hja : X j a = 1) (hab : X a b = 1) (hbc : X b c = 1)
    (hcd : X c d = 1) (hdk : X d k = 1) (u v : ι) :
    X u v =
      (if u ∉ ({a,b,c,d} : Finset ι) ∧ v ∉ ({a,b,c,d} : Finset ι)
        then X u v else 0) +
      edgeIndicator j a u v + edgeIndicator a b u v + edgeIndicator b c u v +
      edgeIndicator c d u v + edgeIndicator d k u v := by
  have h01 : j ≠ a := hnodes.ne (by decide : (0 : Fin 6) ≠ 1)
  have h02 : j ≠ b := hnodes.ne (by decide : (0 : Fin 6) ≠ 2)
  have h03 : j ≠ c := hnodes.ne (by decide : (0 : Fin 6) ≠ 3)
  have h04 : j ≠ d := hnodes.ne (by decide : (0 : Fin 6) ≠ 4)
  have h05 : j ≠ k := hnodes.ne (by decide : (0 : Fin 6) ≠ 5)
  have h12 : a ≠ b := hnodes.ne (by decide : (1 : Fin 6) ≠ 2)
  have h13 : a ≠ c := hnodes.ne (by decide : (1 : Fin 6) ≠ 3)
  have h14 : a ≠ d := hnodes.ne (by decide : (1 : Fin 6) ≠ 4)
  have h15 : a ≠ k := hnodes.ne (by decide : (1 : Fin 6) ≠ 5)
  have h23 : b ≠ c := hnodes.ne (by decide : (2 : Fin 6) ≠ 3)
  have h24 : b ≠ d := hnodes.ne (by decide : (2 : Fin 6) ≠ 4)
  have h25 : b ≠ k := hnodes.ne (by decide : (2 : Fin 6) ≠ 5)
  have h34 : c ≠ d := hnodes.ne (by decide : (3 : Fin 6) ≠ 4)
  have h35 : c ≠ k := hnodes.ne (by decide : (3 : Fin 6) ≠ 5)
  have h45 : d ≠ k := hnodes.ne (by decide : (4 : Fin 6) ≠ 5)
  have ha (w : ι) := row_eq_two_indicators (X a) (hnonneg a) (hrow a) j b h02
    (by rw [hsym, hja]) hab w
  have hb (w : ι) := row_eq_two_indicators (X b) (hnonneg b) (hrow b) a c h13
    (by rw [hsym, hab]) hbc w
  have hc (w : ι) := row_eq_two_indicators (X c) (hnonneg c) (hrow c) b d h24
    (by rw [hsym, hbc]) hcd w
  have hd (w : ι) := row_eq_two_indicators (X d) (hnonneg d) (hrow d) c k h35
    (by rw [hsym, hcd]) hdk w
  by_cases hua : u = a
  · subst u; simpa [edgeIndicator, h01, h12, h13, h14, h15, Ne.symm h12,
      Ne.symm h13, Ne.symm h14, Ne.symm h15, eq_comm] using ha v
  by_cases hub : u = b
  · subst u; simpa [edgeIndicator, h02, h12, h23, h24, h25, Ne.symm h12,
      Ne.symm h23, Ne.symm h24, Ne.symm h25, eq_comm] using hb v
  by_cases huc : u = c
  · subst u; simpa [edgeIndicator, h03, h13, h23, h34, h35, Ne.symm h13,
      Ne.symm h23, Ne.symm h34, Ne.symm h35, eq_comm] using hc v
  by_cases hud : u = d
  · subst u; simpa [edgeIndicator, h04, h14, h24, h34, h45, Ne.symm h14,
      Ne.symm h24, Ne.symm h34, Ne.symm h45, eq_comm] using hd v
  by_cases hva : v = a
  · subst v; rw [hsym u a]; simpa [edgeIndicator, hua, hub, huc, hud, Ne.symm hua, Ne.symm hub, Ne.symm huc, Ne.symm hud,
      h01, h12, h13, h14, h15, eq_comm] using ha u
  by_cases hvb : v = b
  · subst v; rw [hsym u b]; simpa [edgeIndicator, hua, hub, huc, hud, Ne.symm hua, Ne.symm hub, Ne.symm huc, Ne.symm hud,
      h02, h12, h23, h24, h25, eq_comm] using hb u
  by_cases hvc : v = c
  · subst v; rw [hsym u c]; simpa [edgeIndicator, hua, hub, huc, hud, Ne.symm hua, Ne.symm hub, Ne.symm huc, Ne.symm hud,
      h03, h13, h23, h34, h35, eq_comm] using hc u
  by_cases hvd : v = d
  · subst v; rw [hsym u d]; simpa [edgeIndicator, hua, hub, huc, hud, Ne.symm hua, Ne.symm hub, Ne.symm huc, Ne.symm hud,
      h04, h14, h24, h34, h45, eq_comm] using hd u
  simp [edgeIndicator, hua, hub, huc, hud, hva, hvb, hvc, hvd,
    Ne.symm hua, Ne.symm hub, Ne.symm huc, Ne.symm hud,
    Ne.symm hva, Ne.symm hvb, Ne.symm hvc, Ne.symm hvd]

end CircletTSP.Facet.ContractionReduction

namespace CircletTSP.Facet.ContractionReduction
noncomputable section

theorem directed_indicator_sum {n : ℕ} (w : Fin n → Fin n → ℝ) (p q : Fin n) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v then w u v * (if p = u ∧ q = v then 1 else 0) else 0) =
      if p < q then w p q else 0 := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem edgeIndicator_sum {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hw : ∀ u v, w u v = w v u) (p q : Fin n) (hpq : p ≠ q) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v then w u v * edgeIndicator p q u v else 0) = w p q := by
  have he (u v : Fin n) :
      (if u < v then w u v * edgeIndicator p q u v else 0) =
      (if u < v then w u v * (if p = u ∧ q = v then 1 else 0) else 0) +
      (if u < v then w u v * (if q = u ∧ p = v then 1 else 0) else 0) := by
    by_cases h : u < v <;> simp [h, edgeIndicator, mul_add]
  simp_rw [he, Finset.sum_add_distrib, directed_indicator_sum]
  rcases lt_or_gt_of_ne hpq with h | h
  · simp [h, not_lt_of_gt h]
  · simp [h, not_lt_of_gt h, hw q p]

theorem matrix_chain_cost {n : ℕ} (X : Fin n → Fin n → ℝ)
    (hsym : ∀ u v, X u v = X v u)
    (hnonneg : ∀ u v, 0 ≤ X u v) (hrow : ∀ u, ∑ v, X u v = 2)
    (j a b c d k : Fin n) (hnodes : Function.Injective (![j,a,b,c,d,k] : Fin 6 → Fin n))
    (hja : X j a = 1) (hab : X a b = 1) (hbc : X b c = 1)
    (hcd : X c d = 1) (hdk : X d k = 1)
    (w : Fin n → Fin n → ℝ) (hw : ∀ u v, w u v = w v u) :
    (∑ u : Fin n, ∑ v : Fin n, if u < v then w u v * X u v else 0) =
      w j a + w a b + w b c + w c d + w d k +
      ∑ u : Fin n, ∑ v : Fin n,
        if u < v ∧ u ∉ ({a,b,c,d} : Finset (Fin n)) ∧ v ∉ ({a,b,c,d} : Finset (Fin n))
        then w u v * X u v else 0 := by
  have h01 : j ≠ a := hnodes.ne (by decide : (0 : Fin 6) ≠ 1)
  have h12 : a ≠ b := hnodes.ne (by decide : (1 : Fin 6) ≠ 2)
  have h23 : b ≠ c := hnodes.ne (by decide : (2 : Fin 6) ≠ 3)
  have h34 : c ≠ d := hnodes.ne (by decide : (3 : Fin 6) ≠ 4)
  have h45 : d ≠ k := hnodes.ne (by decide : (4 : Fin 6) ≠ 5)
  have hexpand (u v : Fin n) :
      (if u < v then w u v * X u v else 0) =
        (if u < v ∧ u ∉ ({a,b,c,d} : Finset (Fin n)) ∧ v ∉ ({a,b,c,d} : Finset (Fin n))
          then w u v * X u v else 0) +
        (if u < v then w u v * edgeIndicator j a u v else 0) +
        (if u < v then w u v * edgeIndicator a b u v else 0) +
        (if u < v then w u v * edgeIndicator b c u v else 0) +
        (if u < v then w u v * edgeIndicator c d u v else 0) +
        (if u < v then w u v * edgeIndicator d k u v else 0) := by
    conv_lhs => rw [matrix_chain_split X hsym hnonneg hrow j a b c d k hnodes hja hab hbc hcd hdk u v]
    by_cases huv : u < v
    · simp only [huv, if_true, true_and, mul_add, mul_ite, mul_zero]
    · simp [huv]
  simp_rw [hexpand, Finset.sum_add_distrib]
  rw [edgeIndicator_sum w hw j a h01, edgeIndicator_sum w hw a b h12,
    edgeIndicator_sum w hw b c h23, edgeIndicator_sum w hw c d h34,
    edgeIndicator_sum w hw d k h45]
  ring

theorem tour_chain_old_cost {n : ℕ} (hn : 8 ≤ n) (π : Equiv.Perm (Fin n))
    (j a b c d k : Fin n) (hnodes : Function.Injective (![j,a,b,c,d,k] : Fin 6 → Fin n))
    (hja : MetricTSP.tourVec π j a = 1) (hab : MetricTSP.tourVec π a b = 1)
    (hbc : MetricTSP.tourVec π b c = 1) (hcd : MetricTSP.tourVec π c d = 1)
    (hdk : MetricTSP.tourVec π d k = 1)
    (hkeep : ∀ v : Fin n, v.val+1 ∈ keptLabels n ↔ v ∉ ({a,b,c,d} : Finset (Fin n))) :
    circletForm n (MetricTSP.tourVec π) =
      (labCost n (j.val+1) (a.val+1) : ℝ) + (labCost n (a.val+1) (b.val+1) : ℝ) +
      (labCost n (b.val+1) (c.val+1) : ℝ) + (labCost n (c.val+1) (d.val+1) : ℝ) +
      (labCost n (d.val+1) (k.val+1) : ℝ) +
      ∑ u : Fin n, ∑ v : Fin n,
        if u < v ∧ u.val+1∈keptLabels n ∧ v.val+1∈keptLabels n then
          (labCost n (u.val+1) (v.val+1) : ℝ) * MetricTSP.tourVec π u v else 0 := by
  rw [circletForm_eq_labCost_sum]
  simp_rw [hkeep]
  exact matrix_chain_cost (MetricTSP.tourVec π) (TourCounts.tourVec_symm π)
    (TourCounts.tourVec_nonneg π) (TourCounts.tourVec_row_sum (by omega) π)
    j a b c d k hnodes hja hab hbc hcd hdk
    (fun u v => (labCost n (u.val+1) (v.val+1) : ℝ))
    (fun u v => by rw [labCost_symm n (u.val+1) (v.val+1)])

theorem old_cost_one (n : ℕ) (hn : 8 ≤ n) (π : Equiv.Perm (Fin n)) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hjk : j ≠ k)
    (hchain : ChainOne π j k) :
    circletForm n (MetricTSP.tourVec π) =
      ((labCost n j 1 + labCost n 1 2 + labCost n 2 (n/2+2) + labCost n (n/2+2) (n/2+1) + labCost n (n/2+1) k : ℤ) : ℝ) +
      ∑ u : Fin n, ∑ v : Fin n,
        if u < v ∧ u.val+1∈keptLabels n ∧ v.val+1∈keptLabels n then
          (labCost n (u.val+1) (v.val+1) : ℝ) * MetricTSP.tourVec π u v else 0 := by
  have hj' := (ContractTour.kept_iff n j).mp hj
  have hk' := (ContractTour.kept_iff n k).mp hk
  let J : Fin n := ⟨j-1, by omega⟩
  let K : Fin n := ⟨k-1, by omega⟩
  let A : Fin n := ⟨0, by omega⟩
  let B : Fin n := ⟨1, by omega⟩
  let C : Fin n := ⟨n/2+1, by omega⟩
  let D : Fin n := ⟨n/2, by omega⟩
  have hJ : J.val+1 = j := by dsimp [J]; omega
  have hK : K.val+1 = k := by dsimp [K]; omega
  have hnodes : Function.Injective (![J,A,B,C,D,K] : Fin 6 → Fin n) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      first | rfl | (have he := congrArg Fin.val huv; dsimp [J,K,A,B,C,D] at he; omega)
  have hkeep (v : Fin n) : v.val+1 ∈ keptLabels n ↔ v ∉ ({A,B,C,D} : Finset (Fin n)) := by
    rw [ContractTour.kept_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff]
    dsimp [A,B,C,D]
    have hv := v.isLt
    omega
  obtain ⟨e0,e1,e2,e3,e4⟩ := hchain
  have h := tour_chain_old_cost hn π J A B C D K hnodes
    (ContractTour.hasEdge_to_adj π J A j 1 hJ rfl e0)
    (ContractTour.hasEdge_to_adj π A B 1 2 rfl rfl e1)
    (ContractTour.hasEdge_to_adj π B C 2 (n/2+2) rfl rfl e2)
    (ContractTour.hasEdge_to_adj π C D (n/2+2) (n/2+1) rfl rfl e3)
    (ContractTour.hasEdge_to_adj π D K (n/2+1) k rfl hK e4)
    hkeep
  simpa only [hJ, hK, show A.val+1=1 from rfl, show B.val+1=2 from rfl,
    show C.val+1=n/2+2 from rfl, show D.val+1=n/2+1 from rfl, Int.cast_add] using h

theorem old_cost_two (n : ℕ) (hn : 8 ≤ n) (π : Equiv.Perm (Fin n)) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hjk : j ≠ k)
    (hchain : ChainTwo π j k) :
    circletForm n (MetricTSP.tourVec π) =
      ((labCost n j (n/2+2) + labCost n (n/2+2) 2 + labCost n 2 1 + labCost n 1 (n/2+1) + labCost n (n/2+1) k : ℤ) : ℝ) +
      ∑ u : Fin n, ∑ v : Fin n,
        if u < v ∧ u.val+1∈keptLabels n ∧ v.val+1∈keptLabels n then
          (labCost n (u.val+1) (v.val+1) : ℝ) * MetricTSP.tourVec π u v else 0 := by
  have hj' := (ContractTour.kept_iff n j).mp hj
  have hk' := (ContractTour.kept_iff n k).mp hk
  let J : Fin n := ⟨j-1, by omega⟩
  let K : Fin n := ⟨k-1, by omega⟩
  let A : Fin n := ⟨0, by omega⟩
  let B : Fin n := ⟨1, by omega⟩
  let C : Fin n := ⟨n/2+1, by omega⟩
  let D : Fin n := ⟨n/2, by omega⟩
  have hJ : J.val+1 = j := by dsimp [J]; omega
  have hK : K.val+1 = k := by dsimp [K]; omega
  have hnodes : Function.Injective (![J,C,B,A,D,K] : Fin 6 → Fin n) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      first | rfl | (have he := congrArg Fin.val huv; dsimp [J,K,A,B,C,D] at he; omega)
  have hkeep (v : Fin n) : v.val+1 ∈ keptLabels n ↔ v ∉ ({C,B,A,D} : Finset (Fin n)) := by
    rw [ContractTour.kept_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff]
    dsimp [A,B,C,D]
    have hv := v.isLt
    omega
  obtain ⟨e0,e1,e2,e3,e4⟩ := hchain
  have h := tour_chain_old_cost hn π J C B A D K hnodes
    (ContractTour.hasEdge_to_adj π J C j (n/2+2) hJ rfl e0)
    (ContractTour.hasEdge_to_adj π C B (n/2+2) 2 rfl rfl e1)
    (ContractTour.hasEdge_to_adj π B A 2 1 rfl rfl e2)
    (ContractTour.hasEdge_to_adj π A D 1 (n/2+1) rfl rfl e3)
    (ContractTour.hasEdge_to_adj π D K (n/2+1) k rfl hK e4)
    hkeep
  simpa only [hJ, hK, show A.val+1=1 from rfl, show B.val+1=2 from rfl,
    show C.val+1=n/2+2 from rfl, show D.val+1=n/2+1 from rfl, Int.cast_add] using h

end
end CircletTSP.Facet.ContractionReduction



set_option autoImplicit false

namespace CircletTSP.Facet.ContractionReduction

noncomputable section

def pathLossOne (n j k : ℕ) : ℤ :=
  labCost n j 1 + labCost n 1 2 + labCost n 2 (n / 2 + 2) +
    labCost n (n / 2 + 2) (n / 2 + 1) + labCost n (n / 2 + 1) k -
      conCost n (relabel n j) (relabel n k)

def pathLossTwo (n j k : ℕ) : ℤ :=
  labCost n j (n / 2 + 2) + labCost n (n / 2 + 2) 2 + labCost n 2 1 +
    labCost n 1 (n / 2 + 1) + labCost n (n / 2 + 1) k -
      conCost n (relabel n j) (relabel n k)

def survivorGainTerm (n : ℕ) (π : Equiv.Perm (Fin n)) (u v : Fin n) : ℝ :=
  if u < v ∧ u.val + 1 ∈ keptLabels n ∧ v.val + 1 ∈ keptLabels n then
    ((labCost n (u.val + 1) (v.val + 1) -
      conCost n (relabel n (u.val + 1)) (relabel n (v.val + 1)) : ℤ) : ℝ) *
        MetricTSP.tourVec π u v
  else 0

def survivorGain (n : ℕ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ u : Fin n, ∑ v : Fin n, survivorGainTerm n π u v

end
end CircletTSP.Facet.ContractionReduction

namespace CircletTSP.Facet.ContractTour

lemma unrelabel_lt_iff (n : ℕ) (_hn : 8 ≤ n) (a b : Fin (n-4)) :
    unrelabel n a < unrelabel n b ↔ a < b := by
  change (unrelabel n a).val < (unrelabel n b).val ↔ a.val < b.val
  dsimp [unrelabel]
  split_ifs <;> omega

lemma relabel_unrelabel (n : ℕ) (hn : 8 ≤ n) (a : Fin (n-4)) :
    relabel n ((unrelabel n a).val+1) = a.val+1 := by
  have h := lower_label n hn (unrelabel n a) (unrelabel_kept n hn a)
  rw [lower_unrelabel] at h
  exact h.symm

lemma sum_unrelabel (n : ℕ) (hn : 8 ≤ n) (f : Fin n → ℝ) :
    (∑ a : Fin (n-4), f (unrelabel n a)) =
      ∑ u : Fin n, if u.val+1∈keptLabels n then f u else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun a _ => unrelabel n a)
  · intro a _
    simp [unrelabel_kept n hn a]
  · intro a _ b _ hab
    exact unrelabel_injective n hn hab
  · intro u hu
    have hkeep : u.val+1∈keptLabels n := (Finset.mem_filter.mp hu).2
    exact ⟨lower n hn u hkeep, Finset.mem_univ _, unrelabel_lower n hn u hkeep⟩
  · intro a _
    rfl

lemma sum_unrelabel₂ (n : ℕ) (hn : 8 ≤ n) (f : Fin n → Fin n → ℝ) :
    (∑ a : Fin (n-4), ∑ b : Fin (n-4), f (unrelabel n a) (unrelabel n b)) =
      ∑ u : Fin n, ∑ v : Fin n,
        if u.val+1∈keptLabels n ∧ v.val+1∈keptLabels n then f u v else 0 := by
  simp_rw [sum_unrelabel n hn]
  rw [sum_unrelabel n hn (fun u => ∑ v : Fin n, if v.val+1∈keptLabels n then f u v else 0)]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u.val+1∈keptLabels n <;> simp [hu]

end CircletTSP.Facet.ContractTour

namespace CircletTSP.Facet.ContractCost

noncomputable section
open ContractionReduction ContractTour

theorem single_edge_weight_of_lt {n : ℕ} (w : Fin n → Fin n → ℝ)
    (a b : Fin n) (hab : a < b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then w u v else 0) = w a b := by
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

theorem single_edge_weight {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hw : ∀ u v, w u v = w v u) (a b : Fin n) (hab : a ≠ b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then w u v else 0) = w a b := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact single_edge_weight_of_lt w a b h
  · simpa [or_comm, and_comm, hw b a] using single_edge_weight_of_lt w b a h


theorem survivor_reindex (n : ℕ) (hn : 8 ≤ n) (x : Fin n → Fin n → ℝ) :
    (∑ a : Fin (n-4), ∑ b : Fin (n-4),
      if a<b then (conCost n (a.val+1) (b.val+1):ℝ)*x (unrelabel n a) (unrelabel n b) else 0) =
    ∑ u : Fin n, ∑ v : Fin n,
      if u<v ∧ u.val+1∈keptLabels n ∧ v.val+1∈keptLabels n then
        (conCost n (relabel n (u.val+1)) (relabel n (v.val+1)):ℝ)*x u v else 0 := by
  have hterm (a b : Fin (n-4)) :
      (if a<b then (conCost n (a.val+1) (b.val+1):ℝ)*x (unrelabel n a) (unrelabel n b) else 0) =
      if unrelabel n a < unrelabel n b then
        (conCost n (relabel n ((unrelabel n a).val+1))
          (relabel n ((unrelabel n b).val+1)):ℝ)*x (unrelabel n a) (unrelabel n b) else 0 := by
    simp only [unrelabel_lt_iff n hn,relabel_unrelabel n hn]
  simp_rw [hterm]
  rw [sum_unrelabel₂ n hn (fun u v => if u<v then
    (conCost n (relabel n (u.val+1)) (relabel n (v.val+1)):ℝ)*x u v else 0)]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : u<v <;> by_cases hu : u.val+1∈keptLabels n <;>
    by_cases hv : v.val+1∈keptLabels n <;> simp [huv,hu,hv]

def labelVertex (n s : ℕ) (hs : s∈keptLabels n) : Fin n :=
  ⟨s-1, by have h := (kept_iff n s).mp hs; omega⟩

theorem labelVertex_label (n s : ℕ) (hs : s∈keptLabels n) :
    (labelVertex n s hs).val+1=s := by
  have h := (kept_iff n s).mp hs
  dsimp [labelVertex]
  omega

def contractedVertex (n : ℕ) (hn : 8 ≤ n) (s : ℕ) (hs : s∈keptLabels n) : Fin (n-4) :=
  lower n hn (labelVertex n s hs) (by simpa only [labelVertex_label] using hs)

theorem contractedVertex_label (n : ℕ) (hn : 8 ≤ n) (s : ℕ) (hs : s∈keptLabels n) :
    (contractedVertex n hn s hs).val+1=relabel n s := by
  unfold contractedVertex
  rw [lower_label,labelVertex_label]

theorem contractedVertex_ne (n : ℕ) (hn : 8 ≤ n) (j k : ℕ)
    (hj : j∈keptLabels n) (hk : k∈keptLabels n) (hjk : j≠k) :
    contractedVertex n hn j hj ≠ contractedVertex n hn k hk := by
  intro h
  have hv := congrArg (unrelabel n) h
  simp only [contractedVertex,unrelabel_lower] at hv
  have hlabel := congrArg (fun u : Fin n => u.val+1) hv
  simp only [labelVertex_label] at hlabel
  exact hjk hlabel

theorem added_edge_cost (n : ℕ) (hn : 8 ≤ n) (j k : ℕ)
    (hj : j∈keptLabels n) (hk : k∈keptLabels n) (hjk : j≠k) :
    (∑ a : Fin (n-4), ∑ b : Fin (n-4),
      if a<b ∧ ((a.val+1=relabel n j ∧ b.val+1=relabel n k) ∨
        (a.val+1=relabel n k ∧ b.val+1=relabel n j)) then
          (conCost n (a.val+1) (b.val+1):ℝ) else 0) =
      (conCost n (relabel n j) (relabel n k):ℝ) := by
  let a₀ := contractedVertex n hn j hj
  let b₀ := contractedVertex n hn k hk
  have ha (a : Fin (n-4)) : a.val+1=relabel n j ↔ a₀=a := by
    rw [← contractedVertex_label n hn j hj]
    simp only [Fin.ext_iff]
    dsimp [a₀]
    omega
  have hb (a : Fin (n-4)) : a.val+1=relabel n k ↔ b₀=a := by
    rw [← contractedVertex_label n hn k hk]
    simp only [Fin.ext_iff]
    dsimp [b₀]
    omega
  simp only [ha,hb]
  have hs := single_edge_weight
    (fun a b : Fin (n-4) => (conCost n (a.val+1) (b.val+1):ℝ))
    (fun a b => by rw [conCost_symm]) a₀ b₀
    (contractedVertex_ne n hn j k hj hk hjk)
  simpa only [and_comm,a₀,b₀,contractedVertex_label] using hs

theorem contracted_cost (n : ℕ) (hn : 8 ≤ n) (x : Fin n → Fin n → ℝ) (j k : ℕ)
    (hj : j∈keptLabels n) (hk : k∈keptLabels n) (hjk : j≠k) :
    circletForm (n-4) (contract n x j k) =
      (conCost n (relabel n j) (relabel n k):ℝ) +
      ∑ u : Fin n, ∑ v : Fin n,
        if u<v ∧ u.val+1∈keptLabels n ∧ v.val+1∈keptLabels n then
          (conCost n (relabel n (u.val+1)) (relabel n (v.val+1)):ℝ)*x u v else 0 := by
  rw [circletForm_contracted_eq_cost_sum n (by omega)]
  have hsplit (a b : Fin (n-4)) :
      (if a<b then (conCost n (a.val+1) (b.val+1):ℝ)*contract n x j k a b else 0) =
      (if a<b then (conCost n (a.val+1) (b.val+1):ℝ)*x (unrelabel n a) (unrelabel n b) else 0) +
      (if a<b ∧ ((a.val+1=relabel n j ∧ b.val+1=relabel n k) ∨
        (a.val+1=relabel n k ∧ b.val+1=relabel n j)) then
          (conCost n (a.val+1) (b.val+1):ℝ) else 0) := by
    unfold contract
    by_cases hab : a<b <;>
      by_cases he : ((a.val+1=relabel n j ∧ b.val+1=relabel n k) ∨
        (a.val+1=relabel n k ∧ b.val+1=relabel n j)) <;>
      simp [hab,he,mul_add]
  simp_rw [hsplit,Finset.sum_add_distrib]
  rw [survivor_reindex n hn x,added_edge_cost n hn j k hj hk hjk,add_comm]

end
end CircletTSP.Facet.ContractCost

namespace CircletTSP.Facet.ContractCost

noncomputable section
open ContractionReduction

theorem survivor_difference (n : ℕ) (π : Equiv.Perm (Fin n)) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u<v ∧ u.val+1∈keptLabels n ∧ v.val+1∈keptLabels n then
        (labCost n (u.val+1) (v.val+1):ℝ)*MetricTSP.tourVec π u v else 0) -
    (∑ u : Fin n, ∑ v : Fin n,
      if u<v ∧ u.val+1∈keptLabels n ∧ v.val+1∈keptLabels n then
        (conCost n (relabel n (u.val+1)) (relabel n (v.val+1)):ℝ)*
          MetricTSP.tourVec π u v else 0) = survivorGain n π := by
  rw [← Finset.sum_sub_distrib]
  unfold survivorGain
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  unfold survivorGainTerm
  split_ifs <;> simp [Int.cast_sub,sub_mul]

theorem difference_of_old_cost (n : ℕ) (hn : 8 ≤ n) (π : Equiv.Perm (Fin n)) (j k : ℕ)
    (hj : j∈keptLabels n) (hk : k∈keptLabels n) (hjk : j≠k) (oldPath : ℤ)
    (hold : circletForm n (MetricTSP.tourVec π) = (oldPath:ℝ) +
      ∑ u : Fin n, ∑ v : Fin n,
        if u<v ∧ u.val+1∈keptLabels n ∧ v.val+1∈keptLabels n then
          (labCost n (u.val+1) (v.val+1):ℝ)*MetricTSP.tourVec π u v else 0) :
    circletForm n (MetricTSP.tourVec π) -
      circletForm (n-4) (contract n (MetricTSP.tourVec π) j k) =
      ((oldPath-conCost n (relabel n j) (relabel n k):ℤ):ℝ)+survivorGain n π := by
  rw [hold,contracted_cost n hn _ j k hj hk hjk,Int.cast_sub]
  have h := survivor_difference n π
  linarith

end
end CircletTSP.Facet.ContractCost

namespace CircletTSP.Facet.ContractionReduction

noncomputable section

theorem cost_difference_one (n : ℕ) (hn : 8 ≤ n) (π : Equiv.Perm (Fin n)) (j k : ℕ)
    (hj : j∈keptLabels n) (hk : k∈keptLabels n) (hjk : j≠k) (hchain : ChainOne π j k) :
    circletForm n (MetricTSP.tourVec π) -
      circletForm (n-4) (contract n (MetricTSP.tourVec π) j k) =
      (pathLossOne n j k:ℝ)+survivorGain n π := by
  exact ContractCost.difference_of_old_cost n hn π j k hj hk hjk _
    (old_cost_one n hn π j k hj hk hjk hchain)

theorem cost_difference_two (n : ℕ) (hn : 8 ≤ n) (π : Equiv.Perm (Fin n)) (j k : ℕ)
    (hj : j∈keptLabels n) (hk : k∈keptLabels n) (hjk : j≠k) (hchain : ChainTwo π j k) :
    circletForm n (MetricTSP.tourVec π) -
      circletForm (n-4) (contract n (MetricTSP.tourVec π) j k) =
      (pathLossTwo n j k:ℝ)+survivorGain n π := by
  exact ContractCost.difference_of_old_cost n hn π j k hj hk hjk _
    (old_cost_two n hn π j k hj hk hjk hchain)

end
end CircletTSP.Facet.ContractionReduction



namespace CircletTSP.Facet.Cost43

lemma int_abs_cases (x : ℤ) : |x| = if 0 ≤ x then x else -x := by
  split_ifs with h
  · exact abs_of_nonneg h
  · exact abs_of_neg (lt_of_not_ge h)

lemma kept_bounds {n s : ℕ} (hs : s ∈ keptLabels n) :
    (3 ≤ s ∧ s ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ s ≤ n) := by
  simp only [keptLabels, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton] at hs
  omega

lemma labLen_odd {n s t : ℕ} (h4 : 4 ∣ n) :
    labLen n s t % 2 = 1 ↔ s % 2 ≠ t % 2 := by
  have hmod := Nat.mod_eq_zero_of_dvd h4
  simp only [labLen, int_abs_cases, min_def]
  split_ifs <;> omega

lemma length_change {n s t : ℕ} (h4 : 4 ∣ n)
    (hs : s ∈ keptLabels n) (ht : t ∈ keptLabels n) :
    conLen n (relabel n s) (relabel n t) =
      if (3 ≤ s ∧ s ≤ n / 2 ∧ 3 ≤ t ∧ t ≤ n / 2) ∨
          (n / 2 + 3 ≤ s ∧ s ≤ n ∧ n / 2 + 3 ≤ t ∧ t ≤ n)
      then labLen n s t else labLen n s t - 2 := by
  have hs' := kept_bounds hs
  have ht' := kept_bounds ht
  have hmod := Nat.mod_eq_zero_of_dvd h4
  rcases hs' with hs' | hs' <;> rcases ht' with ht' | ht'
  all_goals
    simp (disch := omega) only [relabel, if_pos, if_neg]
    simp only [conLen, labLen, int_abs_cases, min_def]
    split_ifs <;> omega


lemma cost_change {n s t : ℕ} (h4 : 4 ∣ n)
    (hs : s ∈ keptLabels n) (ht : t ∈ keptLabels n) :
    conCost n (relabel n s) (relabel n t) =
      (if ((s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t)) ∧ s % 2 ≠ t % 2 then
          labCost n s t
        else if ((s ≤ n / 2 ∧ n / 2 + 3 ≤ t) ∨ (t ≤ n / 2 ∧ n / 2 + 3 ≤ s)) ∧
            s % 2 = t % 2 then
          labCost n s t
        else labCost n s t - 2) := by
  have hs' := kept_bounds hs
  have ht' := kept_bounds ht
  have hl := length_change h4 hs ht
  have hp := labLen_odd (s := s) (t := t) h4
  have hsame : ((3 ≤ s ∧ s ≤ n / 2 ∧ 3 ≤ t ∧ t ≤ n / 2) ∨
      (n / 2 + 3 ≤ s ∧ s ≤ n ∧ n / 2 + 3 ≤ t ∧ t ≤ n)) ↔
      ((s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t)) := by
    clear hl hp
    omega
  have hcross : ((s ≤ n / 2 ∧ n / 2 + 3 ≤ t) ∨ (t ≤ n / 2 ∧ n / 2 + 3 ≤ s)) ↔
      ¬((s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t)) := by
    clear hl hp hsame
    omega
  simp only [hsame] at hl
  clear hs ht hs' ht' hsame
  simp only [conCost, labCost, hp, hl, hcross]
  by_cases hg : (s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t) <;>
    by_cases he : s % 2 = t % 2 <;> simp [hg, he] <;> omega

end CircletTSP.Facet.Cost43

open CircletTSP.Facet

theorem CircletTSP.Facet.proposition_4_3 (n : ℕ) (_hn : 0 < n) (h4 : 4 ∣ n) (s t : ℕ)
    (hs : s ∈ keptLabels n) (ht : t ∈ keptLabels n) (_hst : s ≠ t) :
    conLen n (relabel n s) (relabel n t) =
        (if (3 ≤ s ∧ s ≤ n / 2 ∧ 3 ≤ t ∧ t ≤ n / 2) ∨
            (n / 2 + 3 ≤ s ∧ s ≤ n ∧ n / 2 + 3 ≤ t ∧ t ≤ n)
          then labLen n s t else labLen n s t - 2) ∧
      conCost n (relabel n s) (relabel n t) =
        (if ((s ≤ n / 2 ∧ t ≤ n / 2) ∨ (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t)) ∧ s % 2 ≠ t % 2 then
            labCost n s t
          else if ((s ≤ n / 2 ∧ n / 2 + 3 ≤ t) ∨ (t ≤ n / 2 ∧ n / 2 + 3 ≤ s)) ∧
              s % 2 = t % 2 then
            labCost n s t
          else labCost n s t - 2) ∧
      conCost n (relabel n s) (relabel n t) ≤ labCost n s t := by
  clear _hn _hst
  have hl := Cost43.length_change h4 hs ht
  have hc := Cost43.cost_change h4 hs ht
  refine ⟨hl, hc, ?_⟩
  clear hs ht h4 hl
  split_ifs at hc <;> omega

namespace CircletTSP.Facet.Cost44
open Cost43

lemma fixed_costs {n : ℕ} (hn : 0 < n) (h4 : 4 ∣ n) :
    labCost n 1 2 + labCost n 2 (n / 2 + 2) +
      labCost n (n / 2 + 2) (n / 2 + 1) = 2 := by
  have hmod := Nat.mod_eq_zero_of_dvd h4
  have h12 : labLen n 1 2 = 1 := by
    simp only [labLen, int_abs_cases, min_def]
    split_ifs <;> omega
  have h2d : labLen n 2 (n / 2 + 2) = (n / 2 : ℕ) := by
    simp only [labLen, int_abs_cases, min_def]
    split_ifs <;> omega
  have hdd : labLen n (n / 2 + 2) (n / 2 + 1) = 1 := by
    simp only [labLen, int_abs_cases, min_def]
    split_ifs <;> omega
  have hdmod : ((n / 2 : ℕ) : ℤ) % 2 = 0 := by omega
  simp only [labCost, h12, h2d, hdd, hdmod]
  norm_num

lemma endpoint_lengths {n s : ℕ} (h4 : 4 ∣ n) (hs : s ∈ keptLabels n) :
    labLen n s 1 = (if s ≤ n / 2 then (s : ℤ) - 1 else n - s + 1) ∧
    labLen n (n / 2 + 1) s =
      (if s ≤ n / 2 then (n / 2 : ℕ) + 1 - (s : ℤ) else s - (n / 2 : ℕ) - 1) := by
  have hs' := kept_bounds hs
  have hmod := Nat.mod_eq_zero_of_dvd h4
  rcases hs' with hs' | hs'
  all_goals
    constructor <;> simp only [labLen, int_abs_cases, min_def] <;> split_ifs <;> omega

set_option maxHeartbeats 1000000 in
lemma endpoint_bound {n j k : ℕ} (h4 : 4 ∣ n)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) :
    2 ≤ labCost n j 1 + labCost n (n / 2 + 1) k -
      conCost n (relabel n j) (relabel n k) := by
  have hj' := kept_bounds hj
  have hk' := kept_bounds hk
  have hmod := Nat.mod_eq_zero_of_dvd h4
  have hl := length_change h4 hj hk
  have hp := labLen_odd (s := j) (t := k) h4
  have hcp : conLen n (relabel n j) (relabel n k) % 2 = 1 ↔ j % 2 ≠ k % 2 := by
    clear hj hk hj' hk'
    rw [hl]
    clear hl h4
    split_ifs <;> omega
  have hA := (endpoint_lengths h4 hj).1
  have hB := (endpoint_lengths h4 hk).2
  clear hj hk hp
  simp only [labCost, labLen_odd h4, conCost, hcp]
  rw [hA, hB, hl]
  clear hA hB hl hcp
  rcases hj' with hj' | hj' <;> rcases hk' with hk' | hk'
  all_goals
    by_cases hjp : j % 2 = 0 <;> by_cases hkp : k % 2 = 0
    all_goals
      simp (disch := omega) only [if_pos, if_neg]
      simp only [labLen, int_abs_cases, min_def]
      split_ifs <;> omega

end CircletTSP.Facet.Cost44

open CircletTSP.Facet

theorem CircletTSP.Facet.proposition_4_4 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hjk : j ≠ k) :
    labCost n j 1 + labCost n 1 2 + labCost n 2 (n / 2 + 2) + labCost n (n / 2 + 2) (n / 2 + 1) +
        labCost n (n / 2 + 1) k - conCost n (relabel n j) (relabel n k) ≥ 4 := by
  have _hjk := hjk
  have hfixed := Cost44.fixed_costs hn h4
  have hend := Cost44.endpoint_bound h4 hj hk
  omega


namespace CircletTSP.Facet.Cost45

def colorOne (n s : ℕ) : Prop :=
  (s ≤ n / 2 ∧ s % 2 = 1) ∨ (n / 2 < s ∧ s % 2 = 0)

instance (n s : ℕ) : Decidable (colorOne n s) := inferInstanceAs (Decidable (_ ∨ _))

def pairCity (n : ℕ) (h4 : 4 ∣ n) (v : Fin n) : Fin n :=
  ⟨if v.val % 2 = 0 then v.val + 1 else v.val - 1, by
    have hv := v.isLt
    have hm := Nat.mod_eq_zero_of_dvd h4
    split_ifs <;> omega⟩

lemma pairCity_involutive (n : ℕ) (h4 : 4 ∣ n) : Function.Involutive (pairCity n h4) := by
  intro v
  apply Fin.ext
  simp only [pairCity]
  split_ifs <;> omega

def pairPerm (n : ℕ) (h4 : 4 ∣ n) : Equiv.Perm (Fin n) :=
  (pairCity_involutive n h4).toPerm

lemma color_pair (n : ℕ) (h4 : 4 ∣ n) (v : Fin n) :
    colorOne n ((pairPerm n h4 v).val + 1) ↔ ¬ colorOne n (v.val + 1) := by
  have hv := v.isLt
  have hm := Nat.mod_eq_zero_of_dvd h4
  change colorOne n ((pairCity n h4 v).val + 1) ↔ ¬ colorOne n (v.val + 1)
  simp only [colorOne, pairCity]
  split_ifs <;> omega

lemma within_mass_equal {ι : Type*} [Fintype ι] (x : ι → ι → ℝ)
    (hx : ∀ u v, x u v = x v u) (hrow : ∀ u, ∑ v, x u v = 2)
    (P : ι → Prop) [DecidablePred P] (σ : Equiv.Perm ι)
    (hσ : ∀ u, P (σ u) ↔ ¬ P u) :
    (∑ u, ∑ v, if P u ∧ P v then x u v else 0) =
      ∑ u, ∑ v, if ¬ P u ∧ ¬ P v then x u v else 0 := by
  have hsplit (Q : ι → Prop) [DecidablePred Q] :
      (∑ u, ∑ v, if Q u ∧ Q v then x u v else 0) +
        (∑ u, ∑ v, if Q u ∧ ¬ Q v then x u v else 0) =
          ∑ u, if Q u then (2 : ℝ) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_add_distrib]
    by_cases hu : Q u
    · simp only [hu, true_and, ite_true]
      have ht (v : ι) : (if Q v then x u v else 0) + (if ¬ Q v then x u v else 0) = x u v := by
        by_cases hv : Q v <;> simp [hv]
      simp_rw [ht]
      exact hrow u
    · simp [hu]
  have hcross : (∑ u, ∑ v, if P u ∧ ¬ P v then x u v else 0) =
      ∑ u, ∑ v, if ¬ P u ∧ P v then x u v else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    simp only [and_comm, hx v u]
  have hcard : (∑ u, if P u then (2 : ℝ) else 0) = ∑ u, if ¬ P u then (2 : ℝ) else 0 := by
    rw [← Equiv.sum_comp σ]
    simp_rw [hσ]
  have hp := hsplit P
  have hn := hsplit (fun u => ¬ P u)
  simp only [not_not] at hn
  linarith

end CircletTSP.Facet.Cost45

namespace CircletTSP.Facet.Cost45

lemma exists_same_color {n : ℕ} (hn : 2 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n))
    (a b : Fin n) (ha : ¬ colorOne n (a.val + 1)) (hb : ¬ colorOne n (b.val + 1))
    (hab : Adj π a b) :
    ∃ u v : Fin n, colorOne n (u.val + 1) ∧ colorOne n (v.val + 1) ∧ Adj π u v := by
  classical
  let P : Fin n → Prop := fun u => colorOne n (u.val + 1)
  let x := MetricTSP.tourVec π
  have hbalance := within_mass_equal x (TourCounts.tourVec_symm π)
    (TourCounts.tourVec_row_sum (by omega) π) P (pairPerm n h4) (color_pair n h4)
  by_contra hnone
  have hzero (u v : Fin n) : (if P u ∧ P v then x u v else 0) = 0 := by
    split_ifs with hP
    · rcases WindowBoundProof.tourVec_zero_or_one hn π u v with h | h
      · exact h
      · exact (hnone ⟨u, v, hP.1, hP.2, h⟩).elim
    · rfl
  have hone : (∑ u : Fin n, ∑ v : Fin n, if P u ∧ P v then x u v else 0) = 0 := by
    simp_rw [hzero]
    simp
  have htwo : (∑ u : Fin n, ∑ v : Fin n, if ¬ P u ∧ ¬ P v then x u v else 0) = 0 :=
    hbalance.symm.trans hone
  have hnn (u v : Fin n) : 0 ≤ (if ¬ P u ∧ ¬ P v then x u v else 0) := by
    split_ifs
    · exact TourCounts.tourVec_nonneg π u v
    · rfl
  have hrows := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ =>
    Finset.sum_nonneg (fun v _ => hnn u v))).mp htwo
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hnn a v)).mp
    (hrows a (Finset.mem_univ _))
  have hz := hrow b (Finset.mem_univ _)
  have hab' : x a b = 1 := hab
  simp only [show ¬ P a from ha, show ¬ P b from hb, and_self, hab'] at hz
  norm_num at hz

lemma adj_two_neighbors {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n))
    (a b c v : Fin n) (hbc : b ≠ c) (hab : Adj π a b) (hac : Adj π a c)
    (hav : Adj π a v) : v = b ∨ v = c := by
  classical
  by_contra h
  have hvb : v ≠ b := fun h' => h (Or.inl h')
  have hvc : v ≠ c := fun h' => h (Or.inr h')
  have hsum : (∑ t ∈ ({b, c, v} : Finset (Fin n)), MetricTSP.tourVec π a t) ≤
      ∑ t : Fin n, MetricTSP.tourVec π a t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun t _ _ => TourCounts.tourVec_nonneg π a t)
  have hb : MetricTSP.tourVec π a b = 1 := hab
  have hc : MetricTSP.tourVec π a c = 1 := hac
  have hv : MetricTSP.tourVec π a v = 1 := hav
  rw [TourCounts.tourVec_row_sum hn π a] at hsum
  simp [hbc, Ne.symm hvb, Ne.symm hvc, hb, hc, hv] at hsum
  norm_num at hsum

lemma adj_of_hasEdge {n s t : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n)
    (hu : u.val + 1 = s) (hv : v.val + 1 = t) (h : HasEdge π s t) : Adj π u v := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have hau : a = u := Fin.ext (by omega)
  have hbv : b = v := Fin.ext (by omega)
  simpa only [Adj, hau, hbv] using hab

lemma same_color_kept_edge (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n)
    (j k : ℕ) (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n)
    (hjcolor : ¬ colorOne n j) (hkcolor : ¬ colorOne n k)
    (π : Equiv.Perm (Fin n)) (hchain : ChainTwo π j k) :
    ∃ s ∈ keptLabels n, ∃ t ∈ keptLabels n,
      HasEdge π s t ∧ colorOne n s ∧ colorOne n t := by
  have hm := Nat.mod_eq_zero_of_dvd h4
  have hjbounds : 1 ≤ j ∧ j ≤ n := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj).1)
  have hkbounds : 1 ≤ k ∧ k ≤ n := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hk).1)
  let A : Fin n := ⟨0, by omega⟩
  let B : Fin n := ⟨1, by omega⟩
  let C : Fin n := ⟨n / 2, by omega⟩
  let D : Fin n := ⟨n / 2 + 1, by omega⟩
  let J : Fin n := ⟨j - 1, by omega⟩
  let K : Fin n := ⟨k - 1, by omega⟩
  have hA : A.val + 1 = 1 := rfl
  have hB : B.val + 1 = 2 := rfl
  have hC : C.val + 1 = n / 2 + 1 := rfl
  have hD : D.val + 1 = n / 2 + 2 := by simp [D]
  have hJ : J.val + 1 = j := by simp only [J]; omega
  have hK : K.val + 1 = k := by simp only [K]; omega
  have hPB : ¬ colorOne n (B.val + 1) := by rw [hB]; simp only [colorOne]; omega
  have hPC : ¬ colorOne n (C.val + 1) := by rw [hC]; simp only [colorOne]; omega
  have hPJ : ¬ colorOne n (J.val + 1) := by simpa only [hJ] using hjcolor
  have hPK : ¬ colorOne n (K.val + 1) := by simpa only [hK] using hkcolor
  have hJD := adj_of_hasEdge π J D hJ hD hchain.1
  have hDB := adj_of_hasEdge π D B hD hB hchain.2.1
  have hBA := adj_of_hasEdge π B A hB hA hchain.2.2.1
  have hAC := adj_of_hasEdge π A C hA hC hchain.2.2.2.1
  have hCK := adj_of_hasEdge π C K hC hK hchain.2.2.2.2
  have hAB : Adj π A B := (TourCounts.tourVec_symm π _ _).trans hBA
  have hDJ : Adj π D J := (TourCounts.tourVec_symm π _ _).trans hJD
  have hBC : B ≠ C := by intro h; have := congrArg Fin.val h; simp only [B, C] at this; omega
  have hJB : J ≠ B := by
    intro h
    have hbad : j = 2 := by rw [← hJ, h, hB]
    simp only [keptLabels, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hj
    exact hj.2 (Or.inr (Or.inl hbad))
  have is_kept (u v : Fin n) (hu : colorOne n (u.val + 1))
      (hv : colorOne n (v.val + 1)) (huv : Adj π u v) : u.val + 1 ∈ keptLabels n := by
    have hubounds : 1 ≤ u.val + 1 ∧ u.val + 1 ≤ n := by have := u.isLt; omega
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr hubounds, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (ha | hb | hc | hd)
    · have heq : u = A := Fin.ext (by simp only [A]; omega)
      subst u
      rcases adj_two_neighbors (by omega : 1 < n) π A B C v hBC hAB hAC huv with h | h
      · subst v; exact hPB hv
      · subst v; exact hPC hv
    · have heq : u = B := Fin.ext (by simp only [B]; omega)
      subst u
      exact hPB hu
    · have heq : u = C := Fin.ext (by simp only [C]; omega)
      subst u
      exact hPC hu
    · have heq : u = D := Fin.ext (by simp only [D]; omega)
      subst u
      rcases adj_two_neighbors (by omega : 1 < n) π D J B v hJB hDJ hDB huv with h | h
      · subst v; exact hPJ hv
      · subst v; exact hPB hv
  obtain ⟨u, v, hu, hv, huv⟩ := exists_same_color (by omega : 2 < n) h4 π C K hPC hPK hCK
  refine ⟨u.val + 1, is_kept u v hu hv huv, v.val + 1,
    is_kept v u hv hu ((TourCounts.tourVec_symm π _ _).trans huv), ?_⟩
  exact ⟨⟨u, v, rfl, rfl, huv⟩, hu, hv⟩

end CircletTSP.Facet.Cost45

namespace CircletTSP.Facet.Cost45

open Cost43

def delta (n j k : ℕ) : ℤ :=
  labCost n j (n / 2 + 2) + labCost n (n / 2 + 2) 2 + labCost n 2 1 +
    labCost n 1 (n / 2 + 1) + labCost n (n / 2 + 1) k -
      conCost n (relabel n j) (relabel n k)

lemma fixed_costs {n : ℕ} (hn : 0 < n) (h4 : 4 ∣ n) :
    labCost n (n / 2 + 2) 2 + labCost n 2 1 + labCost n 1 (n / 2 + 1) = 1 := by
  have hmod := Nat.mod_eq_zero_of_dvd h4
  have hD2 : labLen n (n / 2 + 2) 2 = (n / 2 : ℕ) := by
    simp only [labLen, int_abs_cases, min_def]
    split_ifs <;> omega
  have h21 : labLen n 2 1 = 1 := by
    simp only [labLen, int_abs_cases, min_def]
    split_ifs <;> omega
  have h1C : labLen n 1 (n / 2 + 1) = (n / 2 : ℕ) := by
    simp only [labLen, int_abs_cases, min_def]
    split_ifs <;> omega
  have hdmod : ((n / 2 : ℕ) : ℤ) % 2 = 0 := by omega
  simp only [labCost, hD2, h21, h1C, hdmod]
  norm_num

lemma delta_reduced {n j k : ℕ} (hn : 0 < n) (h4 : 4 ∣ n) :
    delta n j k = labCost n j (n / 2 + 2) + labCost n (n / 2 + 1) k -
      conCost n (relabel n j) (relabel n k) + 1 := by
  have h := fixed_costs hn h4
  unfold delta
  linarith

lemma endpoint_lengths {n s : ℕ} (h4 : 4 ∣ n) (hs : s ∈ keptLabels n) :
    labLen n s (n / 2 + 2) =
      (if s ≤ n / 2 then (n / 2 : ℕ) + 2 - (s : ℤ) else s - (n / 2 : ℕ) - 2) ∧
    labLen n (n / 2 + 1) s =
      (if s ≤ n / 2 then (n / 2 : ℕ) + 1 - (s : ℤ) else s - (n / 2 : ℕ) - 1) := by
  have hs' := kept_bounds hs
  have hmod := Nat.mod_eq_zero_of_dvd h4
  rcases hs' with hs' | hs'
  all_goals
    constructor <;> simp only [labLen, int_abs_cases, min_def] <;> split_ifs <;> omega

set_option maxHeartbeats 1000000 in
lemma delta_arithmetic {n j k : ℕ} (hn : 0 < n) (h4 : 4 ∣ n)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) :
    2 ≤ delta n j k ∧ Even (delta n j k) ∧
      (delta n j k = 2 → ¬ colorOne n j ∧ ¬ colorOne n k) := by
  rw [delta_reduced hn h4]
  have hj' := kept_bounds hj
  have hk' := kept_bounds hk
  have hmod := Nat.mod_eq_zero_of_dvd h4
  have hl := length_change h4 hj hk
  have hcp : conLen n (relabel n j) (relabel n k) % 2 = 1 ↔ j % 2 ≠ k % 2 := by
    have hp := labLen_odd (s := j) (t := k) h4
    clear hj hk hj' hk'
    rw [hl]
    split_ifs <;> omega
  have hA := (endpoint_lengths h4 hj).1
  have hB := (endpoint_lengths h4 hk).2
  clear hj hk
  simp only [Int.even_iff, colorOne, labCost, labLen_odd h4, conCost, hcp]
  rw [hA, hB, hl]
  clear hA hB hl hcp
  rcases hj' with hj' | hj' <;> rcases hk' with hk' | hk'
  all_goals
    by_cases hjp : j % 2 = 0 <;> by_cases hkp : k % 2 = 0
    all_goals
      simp (disch := omega) only [if_pos, if_neg]
      simp only [labLen, int_abs_cases, min_def]
      split_ifs <;> omega

lemma same_color_cost_drop {n s t : ℕ} (h4 : 4 ∣ n)
    (hs : s ∈ keptLabels n) (ht : t ∈ keptLabels n)
    (hsc : colorOne n s) (htc : colorOne n t) :
    conCost n (relabel n s) (relabel n t) = labCost n s t - 2 := by
  have hcost := cost_change h4 hs ht
  have hs' := kept_bounds hs
  have ht' := kept_bounds ht
  have hmod := Nat.mod_eq_zero_of_dvd h4
  simp only [colorOne] at hsc htc
  have hnot₁ : ¬ (((s ≤ n / 2 ∧ t ≤ n / 2) ∨
      (n / 2 + 3 ≤ s ∧ n / 2 + 3 ≤ t)) ∧ s % 2 ≠ t % 2) := by omega
  have hnot₂ : ¬ (((s ≤ n / 2 ∧ n / 2 + 3 ≤ t) ∨
      (t ≤ n / 2 ∧ n / 2 + 3 ≤ s)) ∧ s % 2 = t % 2) := by omega
  simpa only [if_neg hnot₁, if_neg hnot₂] using hcost

end CircletTSP.Facet.Cost45

open CircletTSP.Facet

/-- Proposition 4.5 (p. 17): contracting `{j, d + 2}, {d + 2, 2}, {2, 1}, {1, d + 1}, {d + 1, k}`
into `{j', k'}` lowers the cost of these edges by an even amount that is at least `2` (inequality
(6)); and if it is exactly `2`, then every Hamiltonian cycle containing these five edges has
another edge `{s, t}` with `s, t ∉ {1, 2, d + 1, d + 2}` whose cost drops by `2`
(1-based labels, `d = n / 2`). -/
theorem CircletTSP.Facet.proposition_4_5 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hjk : j ≠ k) :
    2 ≤ labCost n j (n / 2 + 2) + labCost n (n / 2 + 2) 2 + labCost n 2 1 +
        labCost n 1 (n / 2 + 1) + labCost n (n / 2 + 1) k - conCost n (relabel n j) (relabel n k) ∧
      Even (labCost n j (n / 2 + 2) + labCost n (n / 2 + 2) 2 + labCost n 2 1 +
        labCost n 1 (n / 2 + 1) + labCost n (n / 2 + 1) k -
          conCost n (relabel n j) (relabel n k)) ∧
      ∀ π : Equiv.Perm (Fin n), ChainTwo π j k →
        labCost n j (n / 2 + 2) + labCost n (n / 2 + 2) 2 + labCost n 2 1 +
            labCost n 1 (n / 2 + 1) + labCost n (n / 2 + 1) k -
              conCost n (relabel n j) (relabel n k) = 2 →
          ∃ s ∈ keptLabels n, ∃ t ∈ keptLabels n, HasEdge π s t ∧
            conCost n (relabel n s) (relabel n t) = labCost n s t - 2 := by
  have _hjk := hjk
  have harith := Cost45.delta_arithmetic hn h4 hj hk
  refine ⟨harith.1, harith.2.1, ?_⟩
  intro π hchain hdelta
  have hdelta' : Cost45.delta n j k = 2 := hdelta
  obtain ⟨hjcolor, hkcolor⟩ := harith.2.2 hdelta'
  have hn8 : 8 ≤ n := by
    have hjbounds := Cost43.kept_bounds hj
    have hm := Nat.mod_eq_zero_of_dvd h4
    omega
  obtain ⟨s, hs, t, ht, hedge, hsc, htc⟩ :=
    Cost45.same_color_kept_edge n hn8 h4 j k hj hk hjcolor hkcolor π hchain
  exact ⟨s, hs, t, ht, hedge, Cost45.same_color_cost_drop h4 hs ht hsc htc⟩





namespace CircletTSP.Facet.ContractionReduction

theorem rotate_ne_self {n : ℕ} (hn : 1 < n) (i : Fin n) : finRotate n i ≠ i := by
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

theorem tourVec_diagonal_zero {n : ℕ} (hn : 1 < n)
    (π : Equiv.Perm (Fin n)) (u : Fin n) : MetricTSP.tourVec π u u = 0 := by
  have hsteps : MetricTSP.tourSteps π u u = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hi' : π i = u ∧ π (finRotate n i) = u := by
      simpa [MetricTSP.tourSteps] using hi
    exact rotate_ne_self hn i (π.injective (hi'.2.trans hi'.1.symm))
  simp [MetricTSP.tourVec, hsteps]

theorem tourVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = MetricTSP.tourVec π v u := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps, or_comm]

theorem survivorGainTerm_nonneg (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n)
    (π : Equiv.Perm (Fin n)) (u v : Fin n) : 0 ≤ survivorGainTerm n π u v := by
  unfold survivorGainTerm
  split_ifs with h
  · have hne : u.val + 1 ≠ v.val + 1 := by
      have huv : u.val < v.val := h.1
      omega
    have hle := (proposition_4_3 n hn h4 (u.val + 1) (v.val + 1) h.2.1 h.2.2 hne).2.2
    have hdiff : (0 : ℝ) ≤
        ((labCost n (u.val + 1) (v.val + 1) -
          conCost n (relabel n (u.val + 1)) (relabel n (v.val + 1)) : ℤ) : ℝ) := by
      exact_mod_cast sub_nonneg.mpr hle
    apply mul_nonneg hdiff
    unfold MetricTSP.tourVec
    positivity
  · exact le_rfl

theorem survivorGain_nonneg (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n)
    (π : Equiv.Perm (Fin n)) : 0 ≤ survivorGain n π := by
  exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
    survivorGainTerm_nonneg n hn h4 π u v

theorem survivorGainTerm_le (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n)
    (π : Equiv.Perm (Fin n)) (u v : Fin n) : survivorGainTerm n π u v ≤ survivorGain n π := by
  have hrow : survivorGainTerm n π u v ≤ ∑ w, survivorGainTerm n π u w :=
    Finset.single_le_sum (fun w _ => survivorGainTerm_nonneg n hn h4 π u w) (Finset.mem_univ v)
  have htotal : (∑ w, survivorGainTerm n π u w) ≤ survivorGain n π :=
    Finset.single_le_sum
      (fun t _ => Finset.sum_nonneg fun w _ => survivorGainTerm_nonneg n hn h4 π t w)
      (Finset.mem_univ u)
  exact hrow.trans htotal

theorem survivorGain_ge_two_of_edge (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n)
    (π : Equiv.Perm (Fin n)) (s t : ℕ) (hs : s ∈ keptLabels n) (ht : t ∈ keptLabels n)
    (hedge : HasEdge π s t)
    (hdrop : conCost n (relabel n s) (relabel n t) = labCost n s t - 2) :
    2 ≤ survivorGain n π := by
  have hn0 : 0 < n := by omega
  have hn2 : 1 < n := by omega
  have hordered (u v : Fin n) (huv : u < v)
      (hu : u.val + 1 ∈ keptLabels n) (hv : v.val + 1 ∈ keptLabels n)
      (hvalue : MetricTSP.tourVec π u v = 1)
      (hcost : conCost n (relabel n (u.val + 1)) (relabel n (v.val + 1)) =
        labCost n (u.val + 1) (v.val + 1) - 2) : 2 ≤ survivorGain n π := by
    have hterm : survivorGainTerm n π u v = 2 := by
      have hc : u < v ∧ u.val + 1 ∈ keptLabels n ∧ v.val + 1 ∈ keptLabels n := ⟨huv, hu, hv⟩
      simp only [survivorGainTerm, if_pos hc, hvalue, mul_one, hcost]
      norm_num
    exact hterm.symm.trans_le (survivorGainTerm_le n hn0 h4 π u v)
  obtain ⟨u, v, hu, hv, hvalue⟩ := hedge
  have hku : u.val + 1 ∈ keptLabels n := by simpa [hu] using hs
  have hkv : v.val + 1 ∈ keptLabels n := by simpa [hv] using ht
  have hcost : conCost n (relabel n (u.val + 1)) (relabel n (v.val + 1)) =
      labCost n (u.val + 1) (v.val + 1) - 2 := by simpa [hu, hv] using hdrop
  have hne : u ≠ v := by
    intro heq
    subst v
    rw [tourVec_diagonal_zero hn2] at hvalue
    norm_num at hvalue
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hordered u v hlt hku hkv hvalue hcost
  · apply hordered v u hlt hkv hku
    · rw [tourVec_symm]
      exact hvalue
    · rw [conCost_symm n (relabel n (v.val + 1)) (relabel n (u.val + 1)),
        labCost_symm n (v.val + 1) (u.val + 1)]
      exact hcost

theorem contraction_cost_of_accounting (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n)
    (π : Equiv.Perm (Fin n)) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hjk : j ≠ k)
    (hchain : ChainOne π j k ∨ ChainTwo π j k)
    (haccountOne : ChainOne π j k →
      circletForm n (MetricTSP.tourVec π) -
        circletForm (n - 4) (contract n (MetricTSP.tourVec π) j k) =
          (pathLossOne n j k : ℝ) + survivorGain n π)
    (haccountTwo : ChainTwo π j k →
      circletForm n (MetricTSP.tourVec π) -
        circletForm (n - 4) (contract n (MetricTSP.tourVec π) j k) =
          (pathLossTwo n j k : ℝ) + survivorGain n π) :
    circletForm (n - 4) (contract n (MetricTSP.tourVec π) j k) + 4 ≤
      circletForm n (MetricTSP.tourVec π) := by
  have hn0 : 0 < n := by omega
  have hgain := survivorGain_nonneg n hn0 h4 π
  rcases hchain with hchain | hchain
  · have hloss : (4 : ℤ) ≤ pathLossOne n j k := proposition_4_4 n hn0 h4 j k hj hk hjk
    have hlossR : (4 : ℝ) ≤ (pathLossOne n j k : ℝ) := by exact_mod_cast hloss
    have haccount := haccountOne hchain
    linarith
  · obtain ⟨hloss, heven, hextra⟩ := proposition_4_5 n hn0 h4 j k hj hk hjk
    change 2 ≤ pathLossTwo n j k at hloss
    change Even (pathLossTwo n j k) at heven
    have haccount := haccountTwo hchain
    by_cases htwo : pathLossTwo n j k = 2
    · obtain ⟨s, hs, t, ht, hedge, hdrop⟩ := hextra π hchain htwo
      have hgain2 := survivorGain_ge_two_of_edge n hn h4 π s t hs ht hedge hdrop
      have hlossR : (pathLossTwo n j k : ℝ) = 2 := by exact_mod_cast htwo
      linarith
    · have hfour : (4 : ℤ) ≤ pathLossTwo n j k := by
        obtain ⟨r, hr⟩ := heven
        omega
      have hfourR : (4 : ℝ) ≤ (pathLossTwo n j k : ℝ) := by exact_mod_cast hfour
      linarith

end CircletTSP.Facet.ContractionReduction

open CircletTSP.Facet

theorem solution (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n)) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hchain : ChainOne π j k ∨ ChainTwo π j k) :
    (∃ σ : Equiv.Perm (Fin (n - 4)),
      MetricTSP.tourVec σ = contract n (MetricTSP.tourVec π) j k) ∧
    circletForm (n - 4) (contract n (MetricTSP.tourVec π) j k) + 4 ≤
      circletForm n (MetricTSP.tourVec π) := by
  obtain ⟨hσ, hjk⟩ := ContractTour.contract_tour n hn h4 π j k hj hk hchain
  refine ⟨hσ, ContractionReduction.contraction_cost_of_accounting n hn h4 π j k hj hk hjk hchain ?_ ?_⟩
  · exact ContractionReduction.cost_difference_one n hn π j k hj hk hjk
  · exact ContractionReduction.cost_difference_two n hn π j k hj hk hjk
