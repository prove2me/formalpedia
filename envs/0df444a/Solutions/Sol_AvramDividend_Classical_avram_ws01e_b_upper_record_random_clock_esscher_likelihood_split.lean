-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_upper_record_random_clock_esscher_likelihood_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T01:13:45.923914+00:00
-- url     : https://prove2.me/submissions/5d3ff2dd-4505-4b3c-ada3-7bb8b470f2ea

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_random_clock_stopped_density_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)))
    (e : Θ → ℝ≥0) (η : Θ) (hObs : u ≤ e η) :
    Real.exp (θ * X.X (e η) ω -
      (e η : ℝ) * laplaceExponent X.c X.σ X.ν θ) =
    Real.exp (θ * b -
      (u : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
    Real.exp (θ * (X.X (e η) ω - X.X u ω) -
      ((e η - u : ℝ≥0) : ℝ) *
        laplaceExponent X.c X.σ X.ν θ) := by
  have hbHit : X.X u ω = b :=
    firstUpcrossing_value_eq_threshold X b hb ω u hu
  simpa only [hbHit] using
    (avram_ws01e_b_esscher_random_clock_stopped_density_split
      X θ (fun _ : Ω => u) e ω η hObs)
