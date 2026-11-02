-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_bounded_hessian_gaussian_compensator_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:06:04.94517+00:00
-- url     : https://prove2.me/submissions/26e21877-06f6-4ebc-b137-2fce1225526f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Bounded discounted stopped pre-dividend Hessian compensation against the actual
original zero-jump Lévy source, with arbitrary Gaussian coefficient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0)
    (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K) :
    let H : Ω → ℝ := stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    Integrable (fun ω => H ω *
      ((X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 -
        (h : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, H ω * ((X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c) ^ 2 - (h : ℝ) * X.σ ^ 2) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let H : Ω → ℝ := stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hHstop : Measurable[hstop.measurableSpace] H :=
    measurable_stoppedValue
      ((avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable
        X x D hD w C hw q T).isStronglyProgressive) hstop
  have hHg : Measurable H :=
    hHstop.mono hstop.measurableSpace_le le_rfl
  have hY : MemLp Y 2 P :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
      X hν τ hstop B hbounded h
  have hYsq : Integrable (fun ω => Y ω ^ 2) P :=
    (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mp hY
  have hb : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K :=
    Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hHbound ω)
  have hHI : Integrable H P := by
    have hunit : Integrable (fun _ : Ω => (1 : ℝ)) P :=
      integrable_const (1 : ℝ)
    have hm : Integrable (fun ω => H ω * (1 : ℝ)) P :=
      hunit.bdd_mul hHg.aestronglyMeasurable hb
    simpa only [mul_one] using hm
  have hWeightedInt : Integrable (fun ω => H ω * Y ω ^ 2) P :=
    hYsq.bdd_mul hHg.aestronglyMeasurable hb
  change Integrable (fun ω => H ω *
      (Y ω ^ 2 - (h : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, H ω * (Y ω ^ 2 - (h : ℝ) * X.σ ^ 2) ∂P) = 0
  exact
    avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero
      X hν x D hD w C hw q T τ hτ B hbounded h hHI hWeightedInt
