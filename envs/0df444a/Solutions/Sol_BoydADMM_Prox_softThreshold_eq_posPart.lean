-- Prove2me | solution 1 for BoydADMM.Prox.softThreshold_eq_posPart
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T06:53:00.973996+00:00
-- url     : https://prove2.me/submissions/2ccd7d32-4f9b-41e5-93bb-ff5a829b2b30

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open BoydADMM.Prox

theorem solution (κ : ℝ) (hκ : 0 ≤ κ) (a : ℝ) :
    softThreshold κ a = max (a - κ) 0 - max (-a - κ) 0 := by
  unfold softThreshold
  split_ifs with h₁ h₂
  · -- κ < a
    have ha : 0 ≤ a - κ := by linarith
    have hb : -a - κ ≤ 0 := by linarith
    simp [max_eq_left ha, max_eq_right hb]
  · -- a < -κ
    have ha : a - κ ≤ 0 := by linarith
    have hb : 0 ≤ -a - κ := by linarith
    simp [max_eq_right ha, max_eq_left hb]
    ring
  · -- |a| ≤ κ
    have ha : a ≤ κ := le_of_not_gt h₁
    have hb : -κ ≤ a := le_of_not_gt h₂
    have h1 : a - κ ≤ 0 := by linarith
    have h2 : -a - κ ≤ 0 := by linarith
    simp [max_eq_right h1, max_eq_right h2]
