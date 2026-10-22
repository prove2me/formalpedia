-- Prove2me | solution 1 for AvramDividend.Classical.chat03_random_sampled_upper_lintegral_le_killed_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:03:54.93039+00:00
-- url     : https://prove2.me/submissions/c8ccc7d8-43c4-4961-a2a4-82b08d4cc348

import Theorems.Thm_AvramDividend_Classical_chat03_sampled_upper_event_payoff_le_killed_scale
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Integrate the corrected upper-exit comparison at an arbitrary random
sampled time. This includes bounded first-grid exit stopping times.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (T : Ω → ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal
      (if a - x < X.X (T ω) ω then
        Real.exp (-(q * (T ω : ℝ))) * W a else 0) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal
      (if X.X (T ω) ω < -x then 0 else
        Real.exp (-(q * (T ω : ℝ))) *
          W (x + X.X (T ω) ω)) ∂P) := by
  apply lintegral_mono
  intro ω
  exact ENNReal.ofReal_le_ofReal
    (chat03_sampled_upper_event_payoff_le_killed_scale
      X q W hW a x ha (T ω) ω)
