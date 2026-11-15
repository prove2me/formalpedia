-- Prove2me | solution 1 for AvramDividend.Classical.avram_a78_original_positive_time_tilt_physical_jump_poisson_laplace_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:18:51.438387+00:00
-- url     : https://prove2.me/submissions/9795a547-9a6f-4d68-b64d-5dc231835fe9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_a91_original_nonzero_nu_positive_time_tilt_physical_poisson_laplace_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
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
  by_cases hNu : X.ν = 0
  · have hNoJump :=
      avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae
        X hNu
    have hJzero : J =ᵐ[P] (fun _ => (0 : ℝ)) := by
      filter_upwards [hJEq, hNoJump] with ω hJω hNoω
      have hf : (fun u : ℝ≥0 =>
          if 0 < u ∧ u ≤ t then
            X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
          else 0) = (fun _ => (0 : ℝ)) := by
        funext u
        split_ifs with h
        · exact hNoω u h.1
        · rfl
      rw [hf] at hJω
      simpa only [tsum_zero] using hJω
    calc
      (∫ ω, Real.exp (θ * J ω) ∂P) =
          (∫ _ : Ω, (1 : ℝ) ∂P) := by
        apply integral_congr_ae
        filter_upwards [hJzero] with ω hω
        simp [hω]
      _ = 1 := by simp
      _ = Real.exp ((t : ℝ) *
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by
        simp [hNu]
  · exact
      avram_a91_original_nonzero_nu_positive_time_tilt_physical_poisson_laplace_20261114
        X hFinite hNu t ht θ hθ J hJMeas hJEq
