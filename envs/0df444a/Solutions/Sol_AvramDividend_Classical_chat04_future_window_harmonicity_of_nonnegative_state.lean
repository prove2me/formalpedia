-- Prove2me | solution 1 for AvramDividend.Classical.chat04_future_window_harmonicity_of_nonnegative_state
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:34:12.6392+00:00
-- url     : https://prove2.me/submissions/3b6d4abc-087e-48e9-a05a-16929a381874

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_future_window_killed_scale_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_killed_scale_zero_of_negative_start

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-! Positivity localisation for the future-window q-scale harmonicity calculation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u)
    (hWneg : ∀ y : ℝ, y < 0 → W y = 0)
    (hPositive :
       ({ω | 0 ≤ x + X.X s ω}).indicator
         (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
       (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
         W (x + X.X u ω)) | 𝓕 s]) =ᵐ[P]
       ({ω | 0 ≤ x + X.X s ω}).indicator
         (fun ω => W (x + X.X s ω))) :
    P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
       (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
         W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => W (x + X.X s ω)) := by
  let A : Set Ω := {ω | x + X.X s ω < 0}
  let f : Ω → ℝ :=
    ({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω))
  have hA : MeasurableSet[𝓕 s] A := by
    change MeasurableSet[𝓕 s] ((fun ω => x + X.X s ω) ⁻¹' Set.Iio (0 : ℝ))
    exact isOpen_Iio.measurableSet.preimage (measurable_const.add (X.adapted s))
  have hf : Integrable f P :=
    chat04_standing_future_window_killed_scale_integrable
      X hX q hq W hW x s u hsu
  have hzero : A.indicator f = fun _ => (0 : ℝ) := by
    funext ω
    by_cases hn : ω ∈ A
    · rw [Set.indicator_of_mem hn]
      exact chat04_future_window_killed_scale_zero_of_negative_start
        X q x W s u hsu ω hn
    · exact Set.indicator_of_notMem hn _
  have hNeg : A.indicator (P[f | 𝓕 s]) =ᵐ[P] (fun _ => 0) := by
    have hPull := condExp_indicator hf hA
    rw [hzero] at hPull
    simpa using hPull.symm
  filter_upwards [hPositive, hNeg] with ω hp hn
  by_cases hx : 0 ≤ x + X.X s ω
  · have hmem : ω ∈ {ω | 0 ≤ x + X.X s ω} := hx
    simpa only [Set.indicator_of_mem hmem] using hp
  · have hneg : x + X.X s ω < 0 := lt_of_not_ge hx
    have hmem : ω ∈ A := hneg
    have hz : P[f | 𝓕 s] ω = 0 := by
      simpa only [Set.indicator_of_mem hmem] using hn
    change P[f | 𝓕 s] ω = W (x + X.X s ω)
    rw [hz, hWneg _ hneg]
