-- Prove2me | solution 1 for BudgetClock.PostedSym.payment_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:10:31.534088+00:00
-- url     : https://prove2.me/submissions/c45f4f22-9799-4200-b3d1-82162a4bdd8b

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting

set_option autoImplicit false

open BudgetClock.PostedSym

lemma bcp_harm (m : ℕ) : 1 + ((harmonic m : ℚ) : ℝ) < 2 * Real.log ((m : ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
    have := Real.log_two_gt_d9
    linarith
  · have h1 := harmonic_le_one_add_log m
    have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hexp : Real.exp 2 < 7.39 := by
      rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
    have hq : (m : ℝ) * Real.exp 2 < ((m : ℝ) + 2) ^ 2 := by
      have : (m : ℝ) * Real.exp 2 < (m : ℝ) * 7.39 := mul_lt_mul_of_pos_left hexp (by linarith)
      nlinarith [sq_nonneg ((m : ℝ) - 1.7)]
    have hlog := Real.log_lt_log (by positivity) hq
    rw [Real.log_mul (by positivity) (Real.exp_pos 2).ne', Real.log_exp, Real.log_pow] at hlog
    push_cast at hlog
    linarith

lemma bcp_offer_sum (n B : ℝ) (L : ℝ) (m : ℕ) (hL : L = 2 * Real.log n) :
    ∑ k ∈ Finset.range (m + 1), (fun a : ℕ => if a = 0 then B / (2 * Real.log n)
        else B / ((a : ℝ) * 2 * Real.log n)) k =
      B / L * (1 + ((harmonic m : ℚ) : ℝ)) := by
  rw [Finset.sum_range_succ', hL]
  simp only [if_true, Nat.succ_ne_zero, if_false]
  have : ((harmonic m : ℚ) : ℝ) = ∑ i ∈ Finset.range m, ((i : ℝ) + 1)⁻¹ := by
    simp [harmonic]
  rw [this, mul_add, mul_one, Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  field_simp

lemma bcp_main (n : ℕ) (hn : 2 ≤ n) (B : ℝ) (hB : 0 < B) :
    ∑ k ∈ Finset.range (n - 1), offerPrice n B k < B := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hlog : 0 < Real.log ((m + 2 : ℕ) : ℝ) := Real.log_pos (by
    have : (2 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    linarith)
  have e : m + 2 - 1 = m + 1 := by omega
  rw [e]
  have := bcp_offer_sum ((m + 2 : ℕ) : ℝ) B (2 * Real.log ((m + 2 : ℕ) : ℝ)) m rfl
  have h2 : ∑ k ∈ Finset.range (m + 1), offerPrice (m + 2) B k =
      B / (2 * Real.log ((m + 2 : ℕ) : ℝ)) * (1 + ((harmonic m : ℚ) : ℝ)) := by
    rw [← this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold offerPrice
    rfl
  rw [h2]
  have hh := bcp_harm m
  have h3 : 2 * Real.log ((m + 2 : ℕ) : ℝ) = 2 * Real.log ((m : ℝ) + 2) := by push_cast; ring_nf
  rw [h3] at *
  have hpos : 0 < 2 * Real.log ((m : ℝ) + 2) := by
    have := hlog; push_cast at this; linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
  nlinarith

lemma bcp_offer_nonneg (n : ℕ) (hn : 2 ≤ n) (B : ℝ) (hB : 0 < B) (a : ℕ) :
    0 ≤ offerPrice n B a := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith)
  unfold offerPrice
  split_ifs
  · positivity
  · positivity

def BcpInv (n : ℕ) (B : ℝ) (j : Fin n) (s : ScanState n) : Prop :=
  s.count = s.winners.card ∧
    ∑ i ∈ s.winners, s.price i = ∑ k ∈ Finset.range s.count, offerPrice n B k ∧
    s.winners ⊆ Finset.univ.erase j

lemma bcp_step (n : ℕ) (B : ℝ) (c : Fin n → ℝ) (j : Fin n) (s : ScanState n) (i : Fin n)
    (hij : i ≠ j) (hi : i ∉ s.winners) (hs : BcpInv n B j s) :
    BcpInv n B j (step n B c s i) ∧ (step n B c s i).count ≤ s.count + 1 ∧
      (∀ x, x ∉ s.winners → x ≠ i → x ∉ (step n B c s i).winners) := by
  obtain ⟨h1, h2, h3⟩ := hs
  unfold step
  split_ifs with hc
  · refine ⟨⟨?_, ?_, ?_⟩, le_rfl, ?_⟩
    · simp [Finset.card_insert_of_notMem hi, h1]
    · simp only
      rw [Finset.sum_insert hi, Finset.sum_range_succ, ← h2]
      simp only [Function.update_self]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [Function.update_of_ne]
      rintro rfl
      exact hi hx
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp [hij]
      · exact h3 hx
    · intro x hx hxi
      simp [hx, hxi]
  · refine ⟨⟨h1, ?_, h3⟩, Nat.le_succ _, ?_⟩
    · simp only
      rw [← h2]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [Function.update_of_ne]
      rintro rfl
      exact hi hx
    · intro x hx _
      exact hx

lemma bcp_fold (n : ℕ) (B : ℝ) (c : Fin n → ℝ) (j : Fin n) :
    ∀ (l : List (Fin n)) (s : ScanState n), l.Nodup → (∀ i ∈ l, i ≠ j) →
      (∀ i ∈ l, i ∉ s.winners) → BcpInv n B j s →
      BcpInv n B j (l.foldl (step n B c) s) := by
  intro l
  induction l with
  | nil => intro s _ _ _ hs; exact hs
  | cons i l ih =>
    intro s hnd hj hdis hs
    rw [List.foldl_cons]
    have hi : i ∉ s.winners := hdis i (List.mem_cons_self)
    obtain ⟨hs1, _, hs3⟩ := bcp_step n B c j s i (hj i List.mem_cons_self) hi hs
    refine ih _ (List.nodup_cons.1 hnd).2 (fun x hx => hj x (List.mem_cons_of_mem _ hx))
      (fun x hx => hs3 x (hdis x (List.mem_cons_of_mem _ hx)) ?_) hs1
    rintro rfl
    exact (List.nodup_cons.1 hnd).1 hx

theorem solution (n : ℕ) (hn : 2 ≤ n) (B : ℝ) (hB : 0 < B)
    (c : Fin n → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B) (j : Fin n) :
    (∑ i ∈ (scan n B c j).winners, (scan n B c j).price i < B) ∧
    (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i ≤ B) := by
  have hinv : BcpInv n B j (scan n B c j) := by
    unfold scan
    refine bcp_fold n B c j _ _ ?_ ?_ ?_ ?_
    · exact (List.nodup_finRange n).filter _
    · intro i hi
      simpa using (List.mem_filter.1 hi).2
    · intro i _; simp
    · refine ⟨by simp, by simp, by simp⟩
  obtain ⟨h1, h2, h3⟩ := hinv
  have hcount : (scan n B c j).count ≤ n - 1 := by
    rw [h1]
    calc (scan n B c j).winners.card ≤ (Finset.univ.erase j).card := Finset.card_le_card h3
      _ = n - 1 := by simp
  have hfirst : ∑ i ∈ (scan n B c j).winners, (scan n B c j).price i < B := by
    rw [h2]
    refine lt_of_le_of_lt ?_ (bcp_main n hn B hB)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 hcount) (fun k _ _ => bcp_offer_nonneg n hn B hB k)
  refine ⟨hfirst, ?_⟩
  unfold mech5
  simp only
  split_ifs with hz hcj
  · have : (scan n B c j).winners = ∅ := by
      rw [← Finset.card_eq_zero, ← h1]; exact hz
    rw [this]
    simp [hB.le]
  · have : (scan n B c j).winners = ∅ := by
      rw [← Finset.card_eq_zero, ← h1]; exact hz
    rw [this]
    simp [hB.le]
  · exact hfirst.le
