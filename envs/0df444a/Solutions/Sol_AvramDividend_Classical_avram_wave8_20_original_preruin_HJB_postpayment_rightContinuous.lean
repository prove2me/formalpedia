-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:46:49.523207+00:00
-- url     : https://prove2.me/submissions/971c9b31-2898-4c3e-a40c-4246e91c6044

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Actual postpayment HJB value is right-continuous along strict survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => w (x + X.X s ω - rightLimit D s ω))
      {s : ℝ≥0 | t ≤ s ∧ (s : ℝ≥0∞) < ruinTime X x D ω} t := by
  let Y : ℝ≥0 → ℝ := fun s =>
    x + X.X s ω - rightLimit D s ω
  let S : Set ℝ≥0 :=
    {s | t ≤ s ∧ (s : ℝ≥0∞) < ruinTime X x D ω}
  have hXShift :
      ContinuousWithinAt
        (fun s : ℝ≥0 => X.X ((0 : ℝ≥0) + s) ω - X.X 0 ω)
        (Ici t) t :=
    (avram_wave7_01_original_shifted_future_increment_path_cadlag X ω 0).1 t
  have hXCont :
      ContinuousWithinAt (fun s : ℝ≥0 => X.X s ω) (Ici t) t := by
    have hh : ContinuousWithinAt
        (fun s : ℝ≥0 =>
          (X.X ((0 : ℝ≥0) + s) ω - X.X 0 ω) + X.X 0 ω)
        (Ici t) t := hXShift.add continuousWithinAt_const
    simpa only [zero_add, sub_add_cancel] using hh
  have hDCont := dividendStrategy_rightLimit_rightContinuous D hD ω t
  have hYRight : ContinuousWithinAt Y (Ici t) t :=
    (continuousWithinAt_const.add hXCont).sub hDCont
  have hYOn : ContinuousWithinAt Y S t :=
    hYRight.mono (by
      intro s hs
      exact hs.1)
  have hMaps : Set.MapsTo Y S (Ici (0 : ℝ)) := by
    intro s hs
    exact postPaymentReserve_nonnegative_strictly_before_ruin
      X x D hD ω s hs.2
  have hYNonneg : 0 ≤ Y t :=
    postPaymentReserve_nonnegative_strictly_before_ruin
      X x D hD ω t ht
  have hwAt : ContinuousWithinAt w (Ici 0) (Y t) :=
    hw_cont (Y t) hYNonneg
  change ContinuousWithinAt (w ∘ Y) S t
  exact hwAt.comp hYOn hMaps
