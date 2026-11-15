-- Prove2me | solution 1 for AvramDividend.Classical.avram_a91_original_nonzero_nu_positive_time_tilt_physical_poisson_laplace_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:22:49.511368+00:00
-- url     : https://prove2.me/submissions/4e71f339-5d98-4910-8a50-cacd5ca84e7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a92_original_finite_negative_activity_marked_poisson_enumeration_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_chat06_laplace_random_mark_sum_without_pgf_assumption
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
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
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
  obtain ⟨N, Y, r, m, hN, hY, hInd, hLaw, hJ, hMom, hRate⟩ :=
    avram_a92_original_finite_negative_activity_marked_poisson_enumeration_20261114
      X hFinite hNu t ht θ hθ J hJMeas hJEq
  have hInt :=
    (avram_a85_original_physical_negative_jump_exponential_integrable_20261114
      X hFinite t θ (le_of_lt hθ) J hJMeas hJEq).1
  have hAEEq : (fun ω => Real.exp (θ * J ω)) =ᵐ[P]
      (fun ω => Real.exp (θ *
        ∑ j ∈ Finset.range (N ω), Y j ω)) := by
    filter_upwards [hJ] with ω hω
    exact congrArg (fun x : ℝ => Real.exp (θ * x)) hω
  have hSumInt : Integrable (fun ω =>
      Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω)) P :=
    hInt.congr hAEEq
  have hPoisson :=
    chat06_laplace_random_mark_sum_without_pgf_assumption
      P N Y hN hY hInd r hLaw θ m hSumInt hMom
  calc
    (∫ ω, Real.exp (θ * J ω) ∂P) =
        (∫ ω, Real.exp (θ *
          ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) :=
      integral_congr_ae hAEEq
    _ = Real.exp ((r : ℝ) * (m - 1)) := hPoisson
    _ = Real.exp ((t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν)) :=
      congrArg Real.exp hRate
