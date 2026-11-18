-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_negative_mark_count_cell_integral_le_probability_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:11:14.145821+00:00
-- url     : https://prove2.me/submissions/692ad2d5-14d3-4c38-95ba-a2a9a43f3649

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every original physical negative-mark count-cell Laplace weight is dominated by its event mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K) :
    ∀ k : ℕ,
      IntegrableOn (fun ω => Real.exp (θ * J ω))
        {ω : Ω | K ω = k} P ∧
      0 ≤ (∫ ω in {ω : Ω | K ω = k},
        Real.exp (θ * J ω) ∂P) ∧
      (∫ ω in {ω : Ω | K ω = k},
        Real.exp (θ * J ω) ∂P) ≤
        P.real {ω : Ω | K ω = k} := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hBounds :=
    avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
      X hFinite t θ hθ J hJEq
  have hMeas : Measurable (fun ω => Real.exp (θ * J ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hJMeas)
  have hInt : Integrable (fun ω => Real.exp (θ * J ω)) P :=
    (integrable_const (1 : ℝ)).mono hMeas.aestronglyMeasurable (by
      filter_upwards [hBounds] with ω hω
      simpa [Real.norm_eq_abs, abs_of_pos hω.1] using hω.2)
  intro k
  let S : Set Ω := {ω : Ω | K ω = k}
  have hS : MeasurableSet S := hK (measurableSet_singleton k)
  have hIntS : IntegrableOn (fun ω => Real.exp (θ * J ω)) S P :=
    hInt.integrableOn
  have hOne : Integrable (fun _ : Ω => (1 : ℝ)) (P.restrict S) :=
    integrable_const 1
  have hUpper :
      (∫ ω in S, Real.exp (θ * J ω) ∂P) ≤
        (∫ _ in S, (1 : ℝ) ∂P) :=
    integral_mono_ae hIntS hOne (by
      filter_upwards [ae_restrict_of_ae hBounds] with ω hω
      exact hω.2)
  have hNonneg : 0 ≤ (∫ ω in S, Real.exp (θ * J ω) ∂P) :=
    integral_nonneg (fun _ => le_of_lt (Real.exp_pos _))
  refine ⟨hIntS, hNonneg, ?_⟩
  simpa [S, measureReal_def] using hUpper
