-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_true_Qp_full_reward_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:45:05.124044+00:00
-- url     : https://prove2.me/submissions/68cda672-e4a6-4d3b-947f-ae470a0a4c76

import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- For an actual exponential observation clock and arbitrary genuine jointly
measurable terminal Esscher density, every whole-future path reward
disintegrates without losing its path-clock dependence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (p : ℝ) (hp : 0 < p)
    (D F : Ω × ℝ → ℝ≥0∞) (hD : Measurable D) (hF : Measurable F) :
    (∫⁻ z : Ω × ℝ, F z ∂((P.prod (expMeasure p)).withDensity D)) =
      (∫⁻ r : ℝ, (∫⁻ ω : Ω, D (ω, r) * F (ω, r) ∂P)
        ∂(expMeasure p)) := by
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  have hprod : Measurable (fun z : Ω × ℝ => D z * F z) :=
    hD.mul hF
  calc
    (∫⁻ z : Ω × ℝ, F z ∂((P.prod (expMeasure p)).withDensity D)) =
        (∫⁻ z : Ω × ℝ, D z * F z ∂(P.prod (expMeasure p))) := by
      rw [lintegral_withDensity_eq_lintegral_mul]
      · simp only [Pi.mul_apply]
      · exact hD
      · exact hF
    _ = (∫⁻ r : ℝ, (∫⁻ ω : Ω, D (ω, r) * F (ω, r) ∂P)
        ∂(expMeasure p)) := by
      exact lintegral_prod_symm (fun z : Ω × ℝ => D z * F z)
        hprod.aemeasurable
