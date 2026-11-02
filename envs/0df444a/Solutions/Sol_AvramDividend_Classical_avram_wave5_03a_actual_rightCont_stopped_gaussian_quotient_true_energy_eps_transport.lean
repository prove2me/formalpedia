-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_quotient_true_energy_eps_transport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:54:23.749967+00:00
-- url     : https://prove2.me/submissions/4bb46385-0de1-4120-902d-841f1dab0b27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Pointwise Young-square transport, integrated on the actual source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    ε * (∫ ω, (Z θ ω) ^ 2 ∂P) ≤
      ε * (1 + ε) * (∫ ω, (Y ω) ^ 2 ∂P) +
      (1 + ε) * (∫ ω, (Z θ ω - Y ω) ^ 2 ∂P) := by
  dsimp only
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  change ε * (∫ ω, (Z θ ω) ^ 2 ∂P) ≤
    ε * (1 + ε) * (∫ ω, (Y ω) ^ 2 ∂P) +
    (1 + ε) * (∫ ω, (Z θ ω - Y ω) ^ 2 ∂P)
  have hMemY : MemLp Y 2 P :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
      X hν τ hτ T hbounded h
  have hMemZ : MemLp (Z θ) 2 P :=
    (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
      X hν τ hτ T hbounded h θ hθ).1
  have hMemErr : MemLp (fun ω => Z θ ω - Y ω) 2 P :=
    hMemZ.sub hMemY
  have hYsq : Integrable (fun ω => (Y ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hMemY.aestronglyMeasurable).mp hMemY
  have hErrSq : Integrable (fun ω => (Z θ ω - Y ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hMemErr.aestronglyMeasurable).mp hMemErr
  have hA : Integrable (fun ω => (ε * (1 + ε)) * (Y ω) ^ 2) P :=
    hYsq.const_mul (ε * (1 + ε))
  have hB : Integrable (fun ω => (1 + ε) * (Z θ ω - Y ω) ^ 2) P :=
    hErrSq.const_mul (1 + ε)
  have hPoint (ω : Ω) :
      ε * (Z θ ω) ^ 2 ≤
        (ε * (1 + ε)) * (Y ω) ^ 2 +
          (1 + ε) * (Z θ ω - Y ω) ^ 2 := by
    nlinarith [sq_nonneg (ε * Y ω - (Z θ ω - Y ω))]
  have hInt :
      (∫ ω, ε * (Z θ ω) ^ 2 ∂P) ≤
        (∫ ω, (ε * (1 + ε)) * (Y ω) ^ 2 +
          (1 + ε) * (Z θ ω - Y ω) ^ 2 ∂P) :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun ω => mul_nonneg hε (sq_nonneg _)))
      (hA.add hB)
      (Filter.Eventually.of_forall hPoint)
  rw [integral_const_mul, integral_add hA hB,
    integral_const_mul, integral_const_mul] at hInt
  simpa only [mul_assoc] using hInt
