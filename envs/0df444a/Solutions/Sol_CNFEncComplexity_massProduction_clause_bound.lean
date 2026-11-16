-- Prove2me | solution 1 for CNFEncComplexity.massProduction_clause_bound
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T06:43:19.722416+00:00
-- url     : https://prove2.me/submissions/ba9cfa74-1932-4c93-8c3c-03f37c93f49b

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace CNFEncComplexity

theorem massProduction_slotCount_le (b : ℕ) (hb : 1 ≤ b) :
    2 ^ (Nat.clog 2 b + 3) ≤ 16 * b := by
  by_cases h : b = 1
  · subst b
    decide
  have hb' : 1 < b := by omega
  have hk : 0 < Nat.clog 2 b := Nat.clog_pos (by decide) hb'
  have hp := Nat.pow_pred_clog_lt_self (b := 2) (by decide) hb'
  have he : Nat.clog 2 b + 3 = (Nat.clog 2 b).pred + 4 := by
    have hs := Nat.succ_pred_eq_of_pos hk
    omega
  rw [he, pow_add]
  norm_num
  exact (Nat.mul_le_mul_right 16 hp.le).trans_eq (Nat.mul_comm _ _)

private theorem two_times_logb_sqrt_add_two (n b : ℕ) (hb : 1 ≤ b) :
    (n : ℝ) + 1 ≤ 3 * Real.logb 2 (Real.sqrt ((2 : ℝ) ^ n * b) + 2) := by
  let S := Real.sqrt ((2 : ℝ) ^ n * b)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hbs : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hSsq : S ^ 2 = (2 : ℝ) ^ n * b := Real.sq_sqrt (by positivity)
  have hpow : (2 : ℝ) ^ n ≤ (S + 2) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hbs (by positivity : 0 ≤ (2 : ℝ) ^ n)
    rw [mul_one, ← hSsq] at h
    nlinarith only [h, hS]
  have hL : (1 : ℝ) ≤ Real.logb 2 (S + 2) := by
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
      (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ S + 2 by linarith))
  have hn : (n : ℝ) ≤ 2 * Real.logb 2 (S + 2) := by
    simpa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
      (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by positivity : 0 < (2 : ℝ) ^ n) hpow)
  change (n : ℝ) + 1 ≤ 3 * Real.logb 2 (S + 2)
  linarith only [hn, hL]

/-- Sparse slot encodings and the shared neighbor checker fit the bound in Lemma 11. -/
theorem _root_.solution (A D H e j : ℕ) :
    ∃ C K : ℕ, ∀ n b q d : ℕ, 1 ≤ b → b ≤ 2 ^ n → q ≤ 16 * b →
      (d : ℝ) ≤ (D : ℝ) * ((n : ℝ) + 1) ^ e →
      ∀ deg clauses : Fin q → ℕ, (∑ r, deg r) ≤ 2 ^ n * d →
      (∀ r, (clauses r : ℝ) ≤ (A : ℝ) * ((n : ℝ) + 1 + Real.sqrt ((n : ℝ) * deg r))) →
      ∀ checker : ℕ, (checker : ℝ) ≤ (H : ℝ) * (b : ℝ) * ((n : ℝ) + 1) ^ j →
      ((∑ r, clauses r : ℕ) : ℝ) + checker ≤
        (C : ℝ) * (Real.sqrt ((2 : ℝ) ^ n * b) + 1) *
          Real.logb 2 (Real.sqrt ((2 : ℝ) ^ n * b) + 2) ^ K := by
  let K := max (e + 1) j
  let W := A * (16 + 4 * (D + 1)) + H
  refine ⟨W * 3 ^ K, K, ?_⟩
  intro n b q d hb hbN hq hd deg clauses hdeg hclauses checker hchecker
  let S := Real.sqrt ((2 : ℝ) ^ n * b)
  let T := (n : ℝ) + 1
  let L := Real.logb 2 (S + 2)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hT : 1 ≤ T := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hb_le : (b : ℝ) ≤ S := by
    apply Real.le_sqrt_of_sq_le
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hbN) (by positivity)
  have hq' : (q : ℝ) ≤ 16 * (b : ℝ) := by exact_mod_cast hq
  have hqS : (q : ℝ) ≤ 16 * S := hq'.trans (by gcongr)
  have hdeg' : (∑ r : Fin q, (deg r : ℝ)) ≤ (2 : ℝ) ^ n * d := by exact_mod_cast hdeg
  have hsumSqrt : (∑ r : Fin q, Real.sqrt ((n : ℝ) * deg r)) ≤
      4 * S * Real.sqrt ((n : ℝ) * d) := by
    calc
      _ ≤ Real.sqrt (q : ℝ) * Real.sqrt ((n : ℝ) * ∑ r : Fin q, (deg r : ℝ)) := by
        simpa [Finset.mul_sum] using
          (Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin q))
            (f := fun _ => 1) (g := fun r => (n : ℝ) * deg r)
            (fun _ => by norm_num) (fun _ => by positivity))
      _ = Real.sqrt ((q : ℝ) * ((n : ℝ) * ∑ r : Fin q, (deg r : ℝ))) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ q)]
      _ ≤ Real.sqrt ((16 * ((2 : ℝ) ^ n * b)) * ((n : ℝ) * d)) := by
        apply Real.sqrt_le_sqrt
        calc
          _ ≤ (16 * (b : ℝ)) * ((n : ℝ) * ((2 : ℝ) ^ n * d)) := by gcongr
          _ = _ := by ring
      _ = _ := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 16 * ((2 : ℝ) ^ n * b)),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
          show Real.sqrt (16 : ℝ) = 4 by
            rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hnD : (n : ℝ) * d ≤ (D : ℝ) * T ^ (e + 1) := by
    calc
      _ ≤ T * ((D : ℝ) * T ^ e) := by
        exact mul_le_mul (by dsimp [T]; linarith) hd (by positivity) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hsmall : Real.sqrt ((n : ℝ) * d) ≤ (D + 1 : ℝ) * T ^ (e+1) := by
    have hnonneg : 0 ≤ (n : ℝ) * d := by positivity
    have hpow : 1 ≤ T ^ (e+1) := one_le_pow₀ hT
    calc
      _ ≤ (n : ℝ) * d + 1 := (Real.sqrt_le_left (by positivity)).2 (by
        nlinarith only [hnonneg, sq_nonneg ((n : ℝ) * d)])
      _ ≤ _ := by linarith only [hnD, hpow]
  have hsum : ((∑ r, clauses r : ℕ) : ℝ) ≤
      (A : ℝ) * ((q : ℝ) * T + ∑ r : Fin q, Real.sqrt ((n : ℝ) * deg r)) := by
    push_cast
    calc
      _ ≤ ∑ r : Fin q, (A : ℝ) * (T + Real.sqrt ((n : ℝ) * deg r)) :=
        Finset.sum_le_sum fun r _ => hclauses r
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hT1 : T ≤ T ^ K := le_self_pow₀ hT (by dsimp [K]; omega)
  have hTe : T ^ (e+1) ≤ T ^ K := pow_le_pow_right₀ hT (le_max_left _ _)
  have hTj : T ^ j ≤ T ^ K := pow_le_pow_right₀ hT (le_max_right _ _)
  have hSums : ((∑ r, clauses r : ℕ) : ℝ) + checker ≤ (W : ℝ) * S * T ^ K := by
    calc
      _ ≤ (A : ℝ) * ((q : ℝ) * T + ∑ r : Fin q, Real.sqrt ((n : ℝ) * deg r)) +
          (H : ℝ) * b * T ^ j := add_le_add hsum hchecker
      _ ≤ (A : ℝ) * ((16 * S) * T ^ K + 4 * S * ((D + 1 : ℝ) * T ^ K)) +
          (H : ℝ) * S * T ^ K := by
        have hsle := hsumSqrt.trans (mul_le_mul_of_nonneg_left
          (hsmall.trans (mul_le_mul_of_nonneg_left hTe (by positivity))) (by positivity))
        gcongr
      _ = _ := by dsimp [W]; push_cast; ring
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) (by linarith only [hS])
  have hTL : T ≤ 3 * L := two_times_logb_sqrt_add_two n b hb
  calc
    _ ≤ (W : ℝ) * S * T ^ K := hSums
    _ ≤ (W : ℝ) * (S + 1) * (3 * L) ^ K := by
      have hp := pow_le_pow_left₀ (zero_le_one.trans hT) hTL K
      have hSn : S ≤ S + 1 := by linarith
      gcongr
    _ = _ := by push_cast; rw [mul_pow]; ring

end CNFEncComplexity
