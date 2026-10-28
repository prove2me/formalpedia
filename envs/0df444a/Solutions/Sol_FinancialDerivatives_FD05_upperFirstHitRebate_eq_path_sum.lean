-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperFirstHitRebate_eq_path_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:42:30.617928+00:00
-- url     : https://prove2.me/submissions/c445500a-dd80-4a2e-86a6-883745aadb6f

import Definitions.Def_fd05_upperFirstHitRebateTree
import Definitions.Def_fd05_discountedFirstHitRebatePrice
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_weightedPathSum
import Definitions.Def_fd03_constantPayoffTree
import Theorems.Thm_FinancialDerivatives_FD03_european_discounted_path_sum
import Theorems.Thm_FinancialDerivatives_FD03_european_constant
import Mathlib
open FinancialDerivatives.FD03 FinancialDerivatives.FD05

namespace A3S89FDP

noncomputable def hsf (m : BinomialMarket) (S : ℝ) (l : List Bool) : ℝ :=
  l.foldl (fun S b => if b then S * m.up else S * m.down) S

noncomputable def fh (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool)
    (n t : ℕ) (S : ℝ) (l : List Bool) : ℕ :=
  ((List.range (n + 1)).filter (fun s =>
    upperTouch B (hsf m S (l.take s)) monitor (t + s))).headD (n + 1)

lemma fh_cons (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool)
    (n t : ℕ) (S : ℝ) (b : Bool) (l : List Bool) :
    fh m B monitor (n + 1) t S (b :: l) =
      if upperTouch B S monitor t then 0
      else fh m B monitor n (t + 1) (if b then S * m.up else S * m.down) l + 1 := by
  unfold fh
  rw [List.range_succ_eq_map, List.filter_cons]
  have h0 : upperTouch B (hsf m S ((b :: l).take 0)) monitor (t + 0)
      = upperTouch B S monitor t := by simp [hsf]
  rw [h0]
  by_cases h : upperTouch B S monitor t = true
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h, List.filter_map]
    have : ((fun s => upperTouch B (hsf m S ((b :: l).take s)) monitor (t + s)) ∘ Nat.succ)
        = (fun s => upperTouch B (hsf m (if b then S * m.up else S * m.down) (l.take s))
            monitor (t + 1 + s)) := by
      funext s
      simp only [Function.comp, List.take_succ_cons, hsf, List.foldl_cons]
      congr 1
      omega
    rw [this, show n + 1 + 1 = Nat.succ (n + 1) from rfl, List.headD_map]

lemma fh_nil (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool) (t : ℕ) (S : ℝ) :
    fh m B monitor 0 t S [] = if upperTouch B S monitor t then 0 else 1 := by
  unfold fh
  simp [hsf]
  split_ifs <;> rfl

lemma sum_split {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ ω, f ω = ∑ ω, f (Fin.cons true ω) + ∑ ω, f (Fin.cons false ω) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

lemma ofFn_cons' {n : ℕ} (b : Bool) (ω : Fin n → Bool) :
    List.ofFn (Fin.cons b ω : Fin (n + 1) → Bool) = b :: List.ofFn ω := by
  rw [List.ofFn_succ]; simp

lemma hw_cons (m : BinomialMarket) (b : Bool) (l : List Bool) :
    historyWeight m (b :: l) = (if b then upWeight m else 1 - upWeight m) * historyWeight m l := by
  simp [historyWeight]

lemma wps_const (m : BinomialMarket) : ∀ (n : ℕ) (c : ℝ),
    weightedPathSum m n (constantPayoffTree n c) = c := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih => intro c; simp only [constantPayoffTree, weightedPathSum, ih]; ring

lemma sum_w (m : BinomialMarket) : ∀ n : ℕ,
    ∑ ω : Fin n → Bool, historyWeight m (List.ofFn ω) = 1 := by
  intro n
  induction n with
  | zero => simp [historyWeight]
  | succ n ih =>
    rw [sum_split]
    simp only [ofFn_cons', hw_cons, if_true, Bool.false_eq_true, if_false, ← Finset.mul_sum, ih]
    ring

lemma coreR (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool) (Z : ℝ) :
    ∀ (n t : ℕ) (S : ℝ),
    weightedPathSum m n (upperFirstHitRebateTree m B monitor Z n t S) =
      ∑ ω : Fin n → Bool, historyWeight m (List.ofFn ω) *
        (if fh m B monitor n t S (List.ofFn ω) ≤ n
          then Z * m.growth ^ (n - fh m B monitor n t S (List.ofFn ω)) else 0) := by
  intro n
  induction n with
  | zero =>
    intro t S
    simp only [upperFirstHitRebateTree, weightedPathSum, Finset.univ_unique, Finset.sum_singleton,
      List.ofFn_zero, fh_nil]
    simp [historyWeight]
  | succ n ih =>
    intro t S
    by_cases h : upperTouch B S monitor t = true
    · simp only [upperFirstHitRebateTree, h, if_true, wps_const]
      have : ∀ ω : Fin (n + 1) → Bool, fh m B monitor (n + 1) t S (List.ofFn ω) = 0 := by
        intro ω
        rw [List.ofFn_succ, fh_cons, if_pos h]
      simp only [this, Nat.zero_le, if_true, Nat.sub_zero, ← Finset.sum_mul, sum_w, one_mul]
    · simp only [upperFirstHitRebateTree, h, Bool.false_eq_true, if_false, weightedPathSum, ih]
      rw [sum_split, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro ω _ <;>
        rw [ofFn_cons', hw_cons, fh_cons, if_neg h] <;> simp [mul_assoc]

lemma fh_firstUpperHit (m : BinomialMarket) (N : ℕ) (B : ℝ) (monitor : ℕ → Bool)
    (l : List Bool) :
    fh m B monitor N 0 m.initialSpot l = firstUpperHit m N B monitor l := by
  unfold fh firstUpperHit upperTouch
  simp only [zero_add]
  rfl

end A3S89FDP

open A3S89FDP in
theorem solution (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool) (Z : ℝ) :
    europeanValue m N
      (upperFirstHitRebateTree m B monitor Z N 0 m.initialSpot) =
    discountedFirstHitRebatePrice m N B monitor Z := by
  have hg : m.growth ≠ 0 := (m.down_pos.trans m.down_lt_growth).ne'
  rw [european_discounted_path_sum, coreR, discountedFirstHitRebatePrice, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [fh_firstUpperHit, mul_div_assoc]
  congr 1
  split_ifs with hτ
  · rw [← pow_sub_mul_pow m.growth hτ]
    field_simp
  · simp
