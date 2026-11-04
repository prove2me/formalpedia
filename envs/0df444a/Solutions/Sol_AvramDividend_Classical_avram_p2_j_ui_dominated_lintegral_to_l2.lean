-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_dominated_lintegral_to_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:26:04.488527+00:00
-- url     : https://prove2.me/submissions/30b68a63-52b2-4657-b4f5-9155dd452c66

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_squared_enorm_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-! Dominate a real square moment by a nonnegative ENNReal source envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (G : Ω → ENNReal) (B : ℝ≥0)
    (hdom : ∀ᵐ ω ∂P, ‖Y ω‖ₑ ≤ G ω)
    (hB : (∫⁻ ω, (G ω) ^ (2 : ℝ) ∂P) ≤ (B : ENNReal) ^ 2) :
    eLpNorm Y 2 P ≤ (B : ENNReal) := by
  have hpow : ∀ᵐ ω ∂P,
      ‖Y ω‖ₑ ^ (2 : ℝ) ≤ (G ω) ^ (2 : ℝ) := by
    filter_upwards [hdom] with ω hω
    gcongr <;> exact hω
  apply avram_p2_j_ui_lintegral_squared_enorm_bound P Y B
  exact (lintegral_mono_ae hpow).trans hB
