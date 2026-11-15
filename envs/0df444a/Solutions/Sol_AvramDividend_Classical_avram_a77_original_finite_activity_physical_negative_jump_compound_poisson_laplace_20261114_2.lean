-- Prove2me | solution 2 for AvramDividend.Classical.avram_a77_original_finite_activity_physical_negative_jump_compound_poisson_laplace_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:57:48.007299+00:00
-- url     : https://prove2.me/submissions/36aef635-5ca3-4a55-9e62-ce038d08c75b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a91_original_nonzero_nu_positive_time_tilt_physical_poisson_laplace_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae
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
  by_cases ht : 0 < t
  · by_cases hθpos : 0 < θ
    · by_cases hν : X.ν = 0
      · have hJump : J =ᵐ[P] (fun _ => (0 : ℝ)) := by
          filter_upwards [hJEq, avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae
            X hν] with ω hEq hNoJump
          rw [hEq]
          calc
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
                X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
              else 0) = (∑' u : ℝ≥0, (0 : ℝ)) := by
                apply tsum_congr
                intro u
                split_ifs with hu
                · exact hNoJump u hu.1
                · rfl
            _ = 0 := by simp
        calc
          (∫ ω, Real.exp (θ * J ω) ∂P) = ∫ ω, (1 : ℝ) ∂P := by
            apply integral_congr_ae
            filter_upwards [hJump] with ω hω
            simp [hω]
          _ = Real.exp ((t : ℝ) *
             (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by
            simp [hν]
      · exact avram_a91_original_nonzero_nu_positive_time_tilt_physical_poisson_laplace_20261114
          X hFinite hν t ht θ hθpos J hJMeas hJEq
    · have hθzero : θ = 0 := le_antisymm (le_of_not_gt hθpos) hθ
      simp [hθzero]
  · have htzero : t = 0 := le_antisymm (le_of_not_gt ht) (zero_le)
    subst t
    have hJump : J =ᵐ[P] (fun _ => (0 : ℝ)) := by
      filter_upwards [hJEq] with ω hEq
      rw [hEq]
      calc
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ (0 : ℝ≥0) then
            X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
          else 0) = (∑' u : ℝ≥0, (0 : ℝ)) := by
            apply tsum_congr
            intro u
            split_ifs with hu
            · exact False.elim ((not_lt_of_ge hu.2) hu.1)
            · rfl
        _ = 0 := by simp
    calc
      (∫ ω, Real.exp (θ * J ω) ∂P) = ∫ ω, (1 : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hJump] with ω hω
        simp [hω]
      _ = Real.exp ((0 : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by simp
