-- Prove2me | solution 1 for BitDFT.packed_scale_runtime_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T21:58:52.679955+00:00
-- url     : https://prove2.me/submissions/43b251d0-5ef6-423c-bf73-37244d3c0b7a

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic

set_option autoImplicit false
open BitDFT IntMul

/-- The packed implementation's fixed number of large and small multiplier
    calls and linear tape passes fit the advertised transfer-cost expression. -/
theorem solution (M : MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T)
    (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    10 * T (n*q) + 22 * T q + 1000 * (n : ℝ) * q ≤
      1000 * transferCost T n q := by
  have time_nonneg (s : ℕ) (hs : 1 ≤ s) : 0 ≤ T s := by
    obtain ⟨t, ht, _⟩ := hM s hs (List.replicate s false) (List.replicate s false)
      (by simp) (by simp)
    exact le_trans (Nat.cast_nonneg t) ht
  have hnp : 0 ≤ T (n*q) := time_nonneg (n*q) (by nlinarith)
  have hqT : 0 ≤ T q := time_nonneg q hq
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hcoef : 0 ≤ 1000 * (n : ℝ) - 22 := by nlinarith
  have hcalls : 0 ≤ (1000 * (n : ℝ) - 22) * T q := mul_nonneg hcoef hqT
  have hsetup : 0 ≤ (q : ℝ) * (lg q : ℝ)^2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  dsimp [transferCost]
  nlinarith
