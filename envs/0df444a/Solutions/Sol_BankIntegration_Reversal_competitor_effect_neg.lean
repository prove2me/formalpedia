-- Prove2me | solution 1 for BankIntegration.Reversal.competitor_effect_neg
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:23:36.032449+00:00
-- url     : https://prove2.me/submissions/737fc231-1af8-4fd3-8063-597b19b046a6

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

open BankIntegration.Reversal in
theorem solution (lam a1 a2 b1 b2 : ℝ) (n : ℕ)
    (hS : Standing lam a1 a2 b1 b2 n) :
    bankCompetitorEffect lam n (xiStar a1 a2 b1 b2) < 0 := by
  obtain ⟨hlam, ha1, ha2, hb1, hb2, hn⟩ := hS
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxs : 0 < xiStar a1 a2 b1 b2 := by unfold xiStar; positivity
  have hbr : 0 < (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) - ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
    rw [div_sub_div _ _ (by positivity) (by positivity)]
    apply div_pos
    · nlinarith
    · positivity
  have hq : 0 < 1 / (1 + xiStar a1 a2 b1 b2) := by positivity
  unfold bankCompetitorEffect
  have : 0 < lam * (1 / (1 + xiStar a1 a2 b1 b2)) *
    ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) - ((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
    have : 0 < lam := by linarith
    positivity
  linarith [show -lam * (1 / (1 + xiStar a1 a2 b1 b2)) *
    ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) - ((n : ℝ) + 1) / ((n : ℝ) + 2)) =
    -(lam * (1 / (1 + xiStar a1 a2 b1 b2)) *
    ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) - ((n : ℝ) + 1) / ((n : ℝ) + 2))) by ring]
