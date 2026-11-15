-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_original_finite_activity_physical_negative_jump_compound_poisson_laplace_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:56:27.820194+00:00
-- url     : https://prove2.me/submissions/fe784f93-1126-46ed-8ab8-9b829535c1fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a78_original_positive_time_tilt_physical_jump_poisson_laplace_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  by_cases ht : t = 0
  · have hnone (u : ℝ≥0) : ¬ (0 < u ∧ u ≤ t) := by
      intro hu
      have hle := hu.2
      rw [ht] at hle
      exact (not_lt_of_ge hle) hu.1
    have hJzero : J =ᵐ[P] (fun _ => (0 : ℝ)) := by
      filter_upwards [hJEq] with ω hω
      have hfun :
          (fun u : ℝ≥0 =>
            if 0 < u ∧ u ≤ t then
              X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
            else 0) = (fun _ => (0 : ℝ)) := by
        funext u
        simp [hnone u]
      rw [hfun] at hω
      simpa using hω
    calc
      (∫ ω, Real.exp (θ * J ω) ∂P) =
          (∫ _ : Ω, (1 : ℝ) ∂P) := by
            apply integral_congr_ae
            filter_upwards [hJzero] with ω hz
            simp [hz]
      _ = Real.exp ((t : ℝ) *
            (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by
        simp [ht]
  · by_cases hθ0 : θ = 0
    · subst θ
      simp
    · have htpos : 0 < t := lt_of_le_of_ne (by positivity : 0 ≤ t) (Ne.symm ht)
      have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
      exact
        avram_a78_original_positive_time_tilt_physical_jump_poisson_laplace_20261114
          X hFinite t htpos θ hθpos J hJMeas hJEq
