-- Prove2me | solution 1 for CircletTSP.Facet.proposition_4_5
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:31:01.761074+00:00
-- url     : https://prove2.me/submissions/da8460c2-8c35-4277-b9c6-c60806782e1a

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
theorem solution (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (j k : ℕ)
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



