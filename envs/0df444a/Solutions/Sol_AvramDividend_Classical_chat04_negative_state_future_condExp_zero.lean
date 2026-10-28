-- Prove2me | solution 1 for AvramDividend.Classical.chat04_negative_state_future_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:32:11.98434+00:00
-- url     : https://prove2.me/submissions/0c6691c1-879d-41a4-b47a-ed3171d485c6

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_future_window_killed_scale_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_killed_scale_zero_of_negative_start

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-! A negative observed reserve forces the whole conditional killed reward to vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    ({ω | x + X.X s ω < 0}).indicator
      (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
       (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
         W (x + X.X u ω)) | 𝓕 s]) =ᵐ[P] (fun _ => 0) := by
  let A : Set Ω := {ω | x + X.X s ω < 0}
  let f : Ω → ℝ :=
    ({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω))
  have hA : MeasurableSet[𝓕 s] A := by
    change MeasurableSet[𝓕 s] ((fun ω => x + X.X s ω) ⁻¹' Set.Iio (0 : ℝ))
    exact isOpen_Iio.measurableSet.preimage (measurable_const.add (X.adapted s))
  have hf : Integrable f P := by
    exact chat04_standing_future_window_killed_scale_integrable
      X hX q hq W hW x s u hsu
  have hzero : A.indicator f = fun _ => (0 : ℝ) := by
    funext ω
    by_cases hn : ω ∈ A
    · rw [Set.indicator_of_mem hn]
      exact chat04_future_window_killed_scale_zero_of_negative_start
        X q x W s u hsu ω hn
    · exact Set.indicator_of_notMem hn _
  change A.indicator (P[f | 𝓕 s]) =ᵐ[P] (fun _ => 0)
  have hPull := condExp_indicator hf hA
  rw [hzero] at hPull
  simpa using hPull.symm
