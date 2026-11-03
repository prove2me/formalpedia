-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_mean_compensated_X_martingale_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:06:29.852742+00:00
-- url     : https://prove2.me/submissions/d8b6e147-2cfc-497d-b7cc-c6f1bd18b79b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_X_integrable_mean_additivity
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_X_condExp_source_past_eq_Xpast_plus_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The canonical source Lévy process compensated by its own original mean
is a martingale across s to s+t under the genuine source filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hStart : Integrable (X.X s) P)
    (hFuture : Integrable (X.X t) P) :
    P[(fun ω => X.X (s + t) ω -
      (∫ η, X.X (s + t) η ∂P)) | 𝓕 s] =ᵐ[P]
      (fun ω => X.X s ω - (∫ η, X.X s η ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let mStart : ℝ := ∫ η, X.X s η ∂P
  let mFuture : ℝ := ∫ η, X.X t η ∂P
  let mEnd : ℝ := ∫ η, X.X (s + t) η ∂P
  obtain ⟨hEndInt, hMean⟩ :=
    avram_wave7_06_original_X_integrable_mean_additivity
      X s t hStart hFuture
  have hMeanEq : mEnd = mStart + mFuture := hMean
  have hOriginalCond :=
    avram_wave7_06_original_future_X_condExp_source_past_eq_Xpast_plus_mean
      X s t hStart hFuture
  change P[X.X (s + t) | 𝓕 s] =ᵐ[P]
    (fun ω => X.X s ω + mFuture) at hOriginalCond
  have hC : Integrable (fun _ : Ω => mEnd) P :=
    integrable_const mEnd
  have hSub := condExp_sub hEndInt hC (𝓕 s)
  have hConst :
      P[(fun _ : Ω => mEnd) | 𝓕 s] = (fun _ : Ω => mEnd) :=
    condExp_const (𝓕.le s) mEnd
  change P[(fun ω => X.X (s + t) ω - mEnd) | 𝓕 s] =ᵐ[P]
    (fun ω => X.X s ω - mStart)
  filter_upwards [hSub, hOriginalCond] with ω hs he
  calc
    P[(fun η => X.X (s + t) η - mEnd) | 𝓕 s] ω =
        (P[X.X (s + t) | 𝓕 s] -
          P[(fun _ : Ω => mEnd) | 𝓕 s]) ω := hs
    _ = (X.X s ω + mFuture) - mEnd := by
      simpa only [Pi.sub_apply, hConst, he]
    _ = X.X s ω - mStart := by
      rw [hMeanEq]
      ring
