-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_marked_cell_coefficient_between_zero_and_Poisson_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:30:03.757845+00:00
-- url     : https://prove2.me/submissions/ba52c76b-46a7-4017-bcec-b0b2e9e94a97

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
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
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (r : ℝ≥0)
    (hRate : (r : ℝ) = ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :
    ∀ k : ℕ,
      0 ≤ (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) ∧
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) ≤
        (poissonMeasure r).real {k} := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hInt, hBound⟩ :=
    avram_a85_original_physical_negative_jump_exponential_integrable_20261114
      X hFinite t θ hθ J hJMeas hJEq
  have hCountLaw :=
    avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
      X hFinite t (Iio (0 : ℝ)) measurableSet_Iio (Subset.rfl)
      K hK hCount r hRate
  intro k
  let E : Set Ω := {ω | K ω = k}
  have hE : MeasurableSet E := hK (measurableSet_singleton k)
  have hIntE : IntegrableOn (fun ω => Real.exp (θ * J ω)) E P :=
    hInt.integrableOn
  have hOne : IntegrableOn (fun _ : Ω => (1 : ℝ)) E P :=
    integrable_const _
  have hLe : (fun ω : Ω => Real.exp (θ * J ω)) ≤ᵐ[P.restrict E]
      (fun _ : Ω => (1 : ℝ)) := by
    apply ae_restrict_of_ae
    filter_upwards [hBound] with ω hw
    exact hw.2
  have hBoundIntegral :
      (∫ ω in E, Real.exp (θ * J ω) ∂P) ≤
        (∫ ω in E, (1 : ℝ) ∂P) :=
    integral_mono_ae hIntE hOne hLe
  have hConstIntegral :
      (∫ ω in E, (1 : ℝ) ∂P) = (P E).toReal := by
    simp [E, Measure.real, integral_const, smul_eq_mul]
  constructor
  · exact integral_nonneg (fun ω => le_of_lt (Real.exp_pos _))
  · calc
      (∫ ω in E, Real.exp (θ * J ω) ∂P) ≤
          (∫ ω in E, (1 : ℝ) ∂P) := hBoundIntegral
      _ = (P E).toReal := hConstIntegral
      _ = (poissonMeasure r).real {k} := by
        simpa only [E, Measure.real] using congrArg ENNReal.toReal (hCountLaw k)
