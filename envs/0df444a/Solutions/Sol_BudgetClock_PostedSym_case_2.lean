-- Prove2me | solution 1 for BudgetClock.PostedSym.case_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:13:02.050988+00:00
-- url     : https://prove2.me/submissions/2b969cdc-c243-453f-b12e-b5f1d17366b2

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting

set_option autoImplicit false

open BudgetClock.PostedSym

lemma psx_offer_anti (n : ℕ) (hn : 2 ≤ n) (B : ℝ) (hB : 0 < B) (a : ℕ) :
    offerPrice n B (a + 1) ≤ offerPrice n B a := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith)
  unfold offerPrice
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    rw [if_neg (by omega), if_neg (by omega)]
    apply div_le_div_of_nonneg_left hB.le (by positivity)
    push_cast
    nlinarith

def PsxInv (n : ℕ) (B : ℝ) (c : Fin n → ℝ) (P : Finset (Fin n)) (s : ScanState n) : Prop :=
  s.count = s.winners.card ∧ s.winners ⊆ P ∧
    ∀ i ∈ P, i ∉ s.winners → offerPrice n B s.count < c i

lemma psx_step (n : ℕ) (hn : 2 ≤ n) (B : ℝ) (hB : 0 < B) (c : Fin n → ℝ)
    (P : Finset (Fin n)) (s : ScanState n) (i : Fin n) (hi : i ∉ P) (hs : PsxInv n B c P s) :
    PsxInv n B c (insert i P) (step n B c s i) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hiw : i ∉ s.winners := fun h => hi (h2 h)
  unfold step
  split_ifs with hc
  · refine ⟨?_, ?_, ?_⟩
    · simp [Finset.card_insert_of_notMem hiw, h1]
    · exact Finset.insert_subset_insert _ h2
    · intro x hx hxw
      simp only [Finset.mem_insert, not_or] at hxw
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact absurd rfl hxw.1
      · exact lt_of_le_of_lt (psx_offer_anti n hn B hB _) (h3 x hx hxw.2)
  · refine ⟨h1, h2.trans (Finset.subset_insert _ _), ?_⟩
    intro x hx hxw
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact lt_of_not_ge hc
    · exact h3 x hx hxw

lemma psx_fold (n : ℕ) (hn : 2 ≤ n) (B : ℝ) (hB : 0 < B) (c : Fin n → ℝ) :
    ∀ (l : List (Fin n)) (P : Finset (Fin n)) (s : ScanState n), l.Nodup →
      (∀ i ∈ l, i ∉ P) → PsxInv n B c P s →
      PsxInv n B c (P ∪ l.toFinset) (l.foldl (step n B c) s) := by
  intro l
  induction l with
  | nil => intro P s _ _ hs; simpa using hs
  | cons i l ih =>
    intro P s hnd hP hs
    rw [List.foldl_cons]
    have h := ih (insert i P) _ (List.nodup_cons.1 hnd).2 ?_
      (psx_step n hn B hB c P s i (hP i List.mem_cons_self) hs)
    · have e : insert i P ∪ l.toFinset = P ∪ (i :: l).toFinset := by
        ext x; simp
      rwa [e] at h
    · intro x hx hxP
      simp only [Finset.mem_insert] at hxP
      rcases hxP with rfl | hxP
      · exact (List.nodup_cons.1 hnd).1 hx
      · exact hP x (List.mem_cons_of_mem _ hx) hxP

lemma psx_scan (n : ℕ) (hn : 2 ≤ n) (B : ℝ) (hB : 0 < B) (c : Fin n → ℝ) (j : Fin n) :
    (scan n B c j).count = (scan n B c j).winners.card ∧ j ∉ (scan n B c j).winners ∧
      ∀ i, i ≠ j → i ∉ (scan n B c j).winners → offerPrice n B (scan n B c j).count < c i := by
  have h := psx_fold n hn B hB c ((List.finRange n).filter (fun i => i ≠ j)) ∅
    { count := 0, winners := ∅, price := fun _ => 0 } ((List.nodup_finRange n).filter _)
    (by simp) ⟨by simp, by simp, by simp⟩
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · intro hj
    have := h2 hj
    simp at this
  · intro i hij hiw
    exact h3 i (by simp [hij]) hiw

/-- Counting: bidders of `O` outside `W'` each cost more than `p`. -/
lemma psx_count (n : ℕ) (B p : ℝ) (hp : 0 < p) (c : Fin n → ℝ) (hc0 : ∀ i, 0 ≤ c i)
    (W' O : Finset (Fin n)) (hO : ∑ i ∈ O, c i ≤ B) (hrej : ∀ i, i ∉ W' → p < c i) :
    (O.card : ℝ) ≤ W'.card + B / p := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := O) (fun i => i ∈ W')
  have h1 : (O.filter (fun i => i ∈ W')).card ≤ W'.card :=
    Finset.card_le_card (fun x hx => (Finset.mem_filter.1 hx).2)
  have h2 : ((O.filter (fun i => i ∉ W')).card : ℝ) * p ≤ B := by
    calc ((O.filter (fun i => i ∉ W')).card : ℝ) * p
        = ∑ i ∈ O.filter (fun i => i ∉ W'), p := by simp
      _ ≤ ∑ i ∈ O.filter (fun i => i ∉ W'), c i :=
          Finset.sum_le_sum (fun i hi => (hrej i (Finset.mem_filter.1 hi).2).le)
      _ ≤ ∑ i ∈ O, c i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => hc0 i)
      _ ≤ B := hO
  have h2' : ((O.filter (fun i => i ∉ W')).card : ℝ) ≤ B / p := by
    rw [le_div_iff₀ hp]; exact h2
  have : (O.card : ℝ) = (O.filter (fun i => i ∈ W')).card + (O.filter (fun i => i ∉ W')).card := by
    exact_mod_cast hsplit.symm
  rw [this]
  have : ((O.filter (fun i => i ∈ W')).card : ℝ) ≤ W'.card := by exact_mod_cast h1
  linarith

/-- Averaging for nonincreasing nonnegative sequences. -/
lemma psx_avg (N : ℕ) (r : ℕ → ℝ) (hr0 : ∀ k, k < N → 0 ≤ r k)
    (hrd : ∀ k l, k ≤ l → l < N → r l ≤ r k) (a m : ℕ) (ha : 1 ≤ a) (haN : a ≤ N)
    (hmN : m ≤ N) :
    (a : ℝ) * ∑ k ∈ Finset.range m, r k ≤ (max m a : ℕ) * ∑ k ∈ Finset.range a, r k := by
  rcases le_or_gt m a with hma | hma
  · rw [max_eq_right hma]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hma)
      (fun k hk _ => hr0 k (by simp at hk; omega))
  · rw [max_eq_left hma.le]
    have hS : (a : ℝ) * r (a - 1) ≤ ∑ k ∈ Finset.range a, r k := by
      calc (a : ℝ) * r (a - 1) = ∑ k ∈ Finset.range a, r (a - 1) := by simp
        _ ≤ ∑ k ∈ Finset.range a, r k :=
          Finset.sum_le_sum (fun k hk => hrd k (a - 1) (by simp at hk; omega) (by omega))
    have hsplit : ∑ k ∈ Finset.range m, r k =
        ∑ k ∈ Finset.range a, r k + ∑ k ∈ Finset.Ico a m, r k := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le a) hma.le]
    have hT : ∑ k ∈ Finset.Ico a m, r k ≤ ((m - a : ℕ) : ℝ) * r (a - 1) := by
      calc ∑ k ∈ Finset.Ico a m, r k ≤ ∑ k ∈ Finset.Ico a m, r (a - 1) :=
            Finset.sum_le_sum (fun k hk => by
              simp at hk; exact hrd (a - 1) k (by omega) (by omega))
        _ = ((m - a : ℕ) : ℝ) * r (a - 1) := by simp
    rw [hsplit]
    have hma' : ((m - a : ℕ) : ℝ) = (m : ℝ) - a := by
      rw [Nat.cast_sub hma.le]
    rw [hma'] at hT
    have hmapos : (0 : ℝ) ≤ (m : ℝ) - a := by
      have : (a : ℝ) ≤ m := by exact_mod_cast hma.le
      linarith
    have ha0 : (0 : ℝ) ≤ a := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hT ha0, mul_le_mul_of_nonneg_left hS hmapos]

lemma psx_val (n : ℕ) (v : Finset (Fin n) → ℝ) (hv : IsSymmetricSubmodular n v)
    (S W : Finset (Fin n)) (hW : 1 ≤ W.card) (K : ℝ) (hK : 1 ≤ K)
    (hSK : (S.card : ℝ) ≤ K * W.card) : v S ≤ K * v W := by
  obtain ⟨r, hr0, hrd, hvr⟩ := hv
  have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hWn : W.card ≤ n := by simpa using Finset.card_le_univ W
  have h := psx_avg n r hr0 hrd W.card S.card hW hWn hSn
  rw [← hvr, ← hvr] at h
  have hvW : 0 ≤ v W := by
    rw [hvr]; exact Finset.sum_nonneg (fun k hk => hr0 k (by simp at hk; omega))
  have hmax : ((max S.card W.card : ℕ) : ℝ) ≤ K * W.card := by
    rcases le_total S.card W.card with h' | h'
    · rw [max_eq_right h']
      have : (0 : ℝ) ≤ W.card := by positivity
      nlinarith
    · rw [max_eq_left h']; exact hSK
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast hW
  have : (W.card : ℝ) * v S ≤ (W.card : ℝ) * (K * v W) := by
    calc (W.card : ℝ) * v S ≤ ((max S.card W.card : ℕ) : ℝ) * v W := h
      _ ≤ (K * W.card) * v W := mul_le_mul_of_nonneg_right hmax hvW
      _ = (W.card : ℝ) * (K * v W) := by ring
  exact le_of_mul_le_mul_left this hWpos

theorem solution (n : ℕ) (hn : 2 ≤ n) (v : Finset (Fin n) → ℝ) (hv : IsSymmetricSubmodular n v)
    (B : ℝ) (hB : 0 < B) (c : Fin n → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B)
    (j : Fin n) (hsome : 1 ≤ (scan n B c j).count) :
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
      v O ≤ (2 * Real.log n + 2) * v (mech5 n B c j).1 := by
  obtain ⟨h1, _, h3⟩ := psx_scan n hn B hB c j
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith)
  set A := (scan n B c j).count with hA
  have hW : (mech5 n B c j).1 = (scan n B c j).winners := by
    unfold mech5
    simp only
    rw [if_neg (by omega)]
  intro O hO
  rw [hW]
  have hApos : (0 : ℝ) < A := by exact_mod_cast hsome
  have hp : offerPrice n B A = B / ((A : ℝ) * 2 * Real.log n) := by
    simp [offerPrice, show A ≠ 0 by omega]
  have hcnt := psx_count n B (B / ((A : ℝ) * 2 * Real.log n)) (by positivity) c hc0
    (insert j (scan n B c j).winners) O hO (by
    intro i hi
    simp only [Finset.mem_insert, not_or] at hi
    have := h3 i hi.1 hi.2
    rwa [hp] at this)
  have hBB : B / (B / ((A : ℝ) * 2 * Real.log n)) = (A : ℝ) * 2 * Real.log n := by
    field_simp
  rw [hBB] at hcnt
  have hins : ((insert j (scan n B c j).winners).card : ℝ) ≤ A + 1 := by
    have := Finset.card_insert_le j (scan n B c j).winners
    rw [← h1] at this
    exact_mod_cast this
  apply psx_val n v hv O _ (by rw [← h1]; exact hsome) _ (by linarith)
  rw [← h1]
  have : (1 : ℝ) ≤ A := by exact_mod_cast hsome
  nlinarith
