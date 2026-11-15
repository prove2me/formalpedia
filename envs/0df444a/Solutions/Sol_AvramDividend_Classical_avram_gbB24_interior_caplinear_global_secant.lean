-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB24_interior_caplinear_global_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:56:31.865959+00:00
-- url     : https://prove2.me/submissions/e4b03ecc-1476-40ad-a66f-6982fc0b98c4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

theorem solution
    (w : ℝ → ℝ) (b : ℝ)
    (hsec : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ b → t - s ≤ w t - w s)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    t - s ≤
      (if t ≤ b then w t else w b + (t - b)) -
      (if s ≤ b then w s else w b + (s - b)) := by
  by_cases ht : t ≤ b
  · have hsb : s ≤ b := le_trans hst ht
    simpa only [if_pos ht, if_pos hsb] using hsec s t hs hst ht
  · by_cases hsb : s ≤ b
    · have hbase := hsec s b hs hsb le_rfl
      simp only [if_neg ht, if_pos hsb]
      linarith
    · simp only [if_neg ht, if_neg hsb]
      linarith
