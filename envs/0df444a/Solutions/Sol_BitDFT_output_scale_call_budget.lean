-- Prove2me | solution 1 for BitDFT.output_scale_call_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:09:38.7241+00:00
-- url     : https://prove2.me/submissions/810288b6-15fe-4e48-8b56-6ec0d1c032c8

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic

set_option autoImplicit false
open BitDFT IntMul

/-- Two clean q-bit calls per coefficient, plus linear tape passes, fit the
    transfer budget for vector output scaling. -/
theorem solution (M : MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T)
    (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    72 * (n : ℝ) * T q + 1000 * (n : ℝ) * q ≤
      1000 * transferCost T n q := by
  have time_nonneg (s : ℕ) (hs : 1 ≤ s) : 0 ≤ T s := by
    obtain ⟨t, ht, _⟩ := hM s hs (List.replicate s false) (List.replicate s false)
      (by simp) (by simp)
    exact le_trans (Nat.cast_nonneg t) ht
  have hqT : 0 ≤ T q := time_nonneg q hq
  have hnqT : 0 ≤ T (n*q) := time_nonneg (n*q) (by nlinarith)
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hqR : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hsetup : 0 ≤ (q : ℝ) * (lg q : ℝ)^2 :=
    mul_nonneg hqR (sq_nonneg _)
  dsimp [transferCost]
  nlinarith
