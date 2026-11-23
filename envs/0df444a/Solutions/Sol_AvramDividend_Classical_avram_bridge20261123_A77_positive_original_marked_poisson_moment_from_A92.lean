-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_positive_original_marked_poisson_moment_from_A92
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:24:49.845962+00:00
-- url     : https://prove2.me/submissions/61e1b524-cba4-479c-975a-8a13d17cbd79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a92_original_finite_negative_activity_marked_poisson_enumeration_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_chat06_laplace_random_mark_sum_without_pgf_assumption
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general
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
        else 0)
    (hNu : X.ν ≠ 0) (ht : 0 < t) (hθpos : 0 < θ) :
    ∃ (N : Ω → ℕ) (r : ℝ≥0) (m : ℝ),
      HasLaw N (poissonMeasure r) P ∧
      (∫ ω, Real.exp (θ * J ω) ∂P) =
        ∫ ω, m ^ (N ω) ∂P ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨N, Y, r, m, hN, hY, hNY, hLaw, hJSum, hFixed, hRate⟩ :=
    AvramDividend.Classical.avram_a92_original_finite_negative_activity_marked_poisson_enumeration_20261114
      X hFinite hNu t ht θ hθpos J hJMeas hJEq
  have hExpAE :
      (fun ω => Real.exp (θ * J ω)) =ᵐ[P]
        (fun ω => Real.exp
          (θ * ∑ j ∈ Finset.range (N ω), Y j ω)) := by
    filter_upwards [hJSum] with ω hω
    simp only [hω]
  have hIntJ : Integrable (fun ω => Real.exp (θ * J ω)) P :=
    (AvramDividend.Classical.avram_a85_original_physical_negative_jump_exponential_integrable_20261114
      X hFinite t θ hθ J hJMeas hJEq).1
  have hIntSum : Integrable
      (fun ω => Real.exp
        (θ * ∑ j ∈ Finset.range (N ω), Y j ω)) P :=
    hIntJ.congr hExpAE
  have hRandom :=
    AvramDividend.Classical.chat06_laplace_random_mark_sum_without_pgf_assumption
      P N Y hN hY hNY r hLaw θ m hIntSum hFixed
  have hPowMeas : AEStronglyMeasurable
      (fun n : ℕ => m ^ n) (Measure.map N P) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hPowMap :
      (∫ ω, m ^ (N ω) ∂P) =
        ∫ n, m ^ n ∂poissonMeasure r := by
    calc
      (∫ ω, m ^ (N ω) ∂P) =
          ∫ n, m ^ n ∂(Measure.map N P) :=
        (integral_map hN.aemeasurable hPowMeas).symm
      _ = ∫ n, m ^ n ∂poissonMeasure r := by
        rw [hLaw.map_eq]
  refine ⟨N, r, m, hLaw, ?_, hRate⟩
  calc
    (∫ ω, Real.exp (θ * J ω) ∂P) =
        (∫ ω, Real.exp
          (θ * ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) :=
      integral_congr_ae hExpAE
    _ = Real.exp ((r : ℝ) * (m - 1)) := hRandom
    _ = ∫ ω, m ^ (N ω) ∂P := by
      rw [hPowMap, AvramDividend.Classical.chat06_poisson_count_pgf_general]
