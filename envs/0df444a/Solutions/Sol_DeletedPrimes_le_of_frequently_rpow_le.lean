-- Prove2me | solution 1 for DeletedPrimes.le_of_frequently_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:47:35.0178+00:00
-- url     : https://prove2.me/submissions/d93ab7f1-a39d-480d-8a6b-07d487a944a3

import Mathlib
import Definitions.Def_DeletedPrimes_Basic

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {a b c C : ℝ} (hc : 0 < c)
    (h : ∃ᶠ X in atTop, c * X ^ a ≤ C * X ^ b) : a ≤ b := by
  by_contra hab
  push Not at hab
  have hlim : Tendsto (fun X : ℝ => X ^ (a - b)) atTop atTop := tendsto_rpow_atTop (by linarith)
  have hev : ∀ᶠ X in atTop, C / c + 1 ≤ X ^ (a - b) ∧ 1 ≤ X := by
    filter_upwards [hlim.eventually_ge_atTop (C / c + 1), eventually_ge_atTop 1] with X h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨X, hX, h1, h2⟩ := (h.and_eventually hev).exists
  have hX0 : 0 < X := by linarith
  have hb : 0 < X ^ b := Real.rpow_pos_of_pos hX0 b
  have hsplit : X ^ a = X ^ (a - b) * X ^ b := by
    rw [← Real.rpow_add hX0]; ring_nf
  rw [hsplit] at hX
  have : c * (C / c + 1) * X ^ b ≤ c * X ^ (a - b) * X ^ b := by
    apply mul_le_mul_of_nonneg_right _ hb.le
    exact mul_le_mul_of_nonneg_left h1 hc.le
  have : (C + c) * X ^ b ≤ C * X ^ b := by
    calc (C + c) * X ^ b = c * (C / c + 1) * X ^ b := by field_simp
      _ ≤ c * X ^ (a - b) * X ^ b := this
      _ = c * (X ^ (a - b) * X ^ b) := by ring
      _ ≤ C * X ^ b := hX
  nlinarith
end DeletedPrimes
