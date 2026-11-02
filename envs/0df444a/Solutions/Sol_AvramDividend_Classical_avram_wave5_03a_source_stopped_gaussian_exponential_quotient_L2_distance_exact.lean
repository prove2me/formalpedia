-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:44:19.388936+00:00
-- url     : https://prove2.me/submissions/5c3bd915-ce27-4ef9-a01f-4a56e72f1943

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact L2 distance of two same-path stopped source Gaussian exponential quotients. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    (∫ ω, (Z θ ω - Z η ω) ^ 2 ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2 +
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * η ^ 2)) - 1) / η ^ 2 -
      2 * ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η)) := by
  dsimp only
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  change (∫ ω, (Z θ ω - Z η ω) ^ 2 ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2 +
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * η ^ 2)) - 1) / η ^ 2 -
      2 * ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η))
  have hMemθ : MemLp (Z θ) 2 P :=
    (avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2
      X hν τ hτ T hbounded h θ hθ).1
  have hMemη : MemLp (Z η) 2 P :=
    (avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2
      X hν τ hτ T hbounded h η hη).1
  have hθSq : Integrable (fun ω => (Z θ ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hMemθ.aestronglyMeasurable).mp hMemθ
  have hηSq : Integrable (fun ω => (Z η ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hMemη.aestronglyMeasurable).mp hMemη
  have hCross : Integrable (fun ω => Z θ ω * Z η ω) P :=
    MemLp.integrable_mul (p := 2) (q := 2) hMemθ hMemη
  have hθE : (∫ ω, (Z θ ω) ^ 2 ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2 := by
    simpa only [pow_two, mul_assoc] using
      (avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy
        X hν τ hτ T hbounded h θ θ hθ hθ)
  have hηE : (∫ ω, (Z η ω) ^ 2 ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * η ^ 2)) - 1) / η ^ 2 := by
    simpa only [pow_two, mul_assoc] using
      (avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy
        X hν τ hτ T hbounded h η η hη hη)
  have hCrossE : (∫ ω, Z θ ω * Z η ω ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η) :=
    avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy
      X hν τ hτ T hbounded h θ η hθ hη
  calc
    (∫ ω, (Z θ ω - Z η ω) ^ 2 ∂P) =
        (∫ ω, (Z θ ω) ^ 2 + (Z η ω) ^ 2 -
          (Z θ ω * Z η ω) * 2 ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = (∫ ω, (Z θ ω) ^ 2 ∂P) +
        (∫ ω, (Z η ω) ^ 2 ∂P) -
        (∫ ω, Z θ ω * Z η ω ∂P) * 2 := by
      calc
        _ = (∫ ω, (Z θ ω) ^ 2 + (Z η ω) ^ 2 ∂P) -
            (∫ ω, (Z θ ω * Z η ω) * 2 ∂P) := by
          exact integral_sub (hθSq.add hηSq) (hCross.mul_const 2)
        _ = _ := by
          rw [integral_add hθSq hηSq, integral_mul_const]
    _ = _ := by
      rw [hθE, hηE, hCrossE]
      ring
