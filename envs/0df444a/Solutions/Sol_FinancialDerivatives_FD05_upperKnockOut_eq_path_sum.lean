-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperKnockOut_eq_path_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:42:11.363681+00:00
-- url     : https://prove2.me/submissions/40e7cb97-c493-4be2-bc96-37103fadf252

import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_discountedSurvivalPathPrice
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_weightedPathSum
import Theorems.Thm_FinancialDerivatives_FD03_european_discounted_path_sum
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

lemma core (m : BinomialMarket) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    ∀ (n t : ℕ) (S : ℝ) (hit : Bool),
    weightedPathSum m n (upperKnockOutTree m B monitor g n t S hit) =
      ∑ ω : Fin n → Bool, historyWeight m (List.ofFn ω) *
        (if hit = false ∧ n < fh m B monitor n t S (List.ofFn ω)
          then g (hsf m S (List.ofFn ω)) else 0) := by
  intro n
  induction n with
  | zero =>
    intro t S hit
    simp only [upperKnockOutTree, weightedPathSum, Finset.univ_unique, Finset.sum_singleton,
      List.ofFn_zero, fh_nil]
    simp [historyWeight, hsf]
    cases hit <;> cases upperTouch B S monitor t <;> simp
  | succ n ih =>
    intro t S hit
    simp only [upperKnockOutTree, weightedPathSum, ih]
    rw [sum_split, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro ω _ <;>
      rw [ofFn_cons', hw_cons, fh_cons] <;>
      cases hit <;> cases upperTouch B S monitor t <;> simp [hsf, mul_assoc]

lemma fh_firstUpperHit (m : BinomialMarket) (N : ℕ) (B : ℝ) (monitor : ℕ → Bool)
    (l : List Bool) :
    fh m B monitor N 0 m.initialSpot l = firstUpperHit m N B monitor l := by
  unfold fh firstUpperHit upperTouch
  simp only [zero_add]
  rfl

end A3S89FDP

open A3S89FDP in
theorem solution (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) =
    discountedSurvivalPathPrice m N B monitor g := by
  rw [european_discounted_path_sum, core, discountedSurvivalPathPrice, div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [fh_firstUpperHit]
  simp only [true_and]
  rfl
