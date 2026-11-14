-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_zero_shifted_negative_mark_loss_uniformly_bounded_by_candidate_increment_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:24.003255+00:00
-- url     : https://prove2.me/submissions/783fdb02-d847-499e-8819-b2d28798c588

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hmono : MonotoneOn w (Icc (0 : ℝ) ε)) :
    ∀ y ∈ Ioc (0 : ℝ) ε, ∀ z : ℝ, z < 0 →
      0 ≤ (w y - w 0) -
        (if y + z < 0 then 0 else w (y + z) - w 0) ∧
      (w y - w 0) -
        (if y + z < 0 then 0 else w (y + z) - w 0) ≤ w ε - w 0 := by
  intro y hy z hz
  have hzero : (0 : ℝ) ∈ Icc 0 ε := ⟨le_rfl, le_of_lt hε⟩
  have hyband : y ∈ Icc (0 : ℝ) ε := ⟨le_of_lt hy.1, hy.2⟩
  have hlow : w 0 ≤ w y :=
    hmono hzero hyband (le_of_lt hy.1)
  have hhigh : w y ≤ w ε :=
    hmono hyband ⟨le_of_lt hε, le_rfl⟩ hy.2
  by_cases hc : y + z < 0
  · simp only [if_pos hc]
    constructor <;> linarith
  · have hpost0 : 0 ≤ y + z := le_of_not_gt hc
    have hposty : y + z ≤ y := by linarith
    have hpost : y + z ∈ Icc (0 : ℝ) ε :=
      ⟨hpost0, hposty.trans hy.2⟩
    have hpostlow : w 0 ≤ w (y + z) :=
      hmono hzero hpost hpost0
    have hposthigh : w (y + z) ≤ w y :=
      hmono hpost hyband hposty
    simp only [if_neg hc]
    constructor <;> linarith
