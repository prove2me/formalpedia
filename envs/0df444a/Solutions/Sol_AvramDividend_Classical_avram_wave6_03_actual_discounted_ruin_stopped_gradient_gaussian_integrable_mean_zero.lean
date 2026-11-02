-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_gradient_gaussian_integrable_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:13:14.860394+00:00
-- url     : https://prove2.me/submissions/ca0c68cd-2b0c-4f3e-ad0a-2182b72acfcc

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact integrable centred Gaussian gradient cell for the original discounted,
ruin-stopped dividend reserve under a bounded source localisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K) :
    let H : Ω → ℝ := stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let Y : Ω → ℝ := fun ω =>
        X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => H ω * Y ω) P ∧
      (∫ ω, H ω * Y ω ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let H : Ω → ℝ := stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))
  let Y : Ω → ℝ := fun ω =>
        X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hHstop : Measurable[hstop.measurableSpace] H :=
    measurable_stoppedValue
      ((avram_wave3_04_source_stopped_discounted_deriv_predictable
        X x D hD w q T).isStronglyProgressive) hstop
  have hHg : Measurable H :=
    hHstop.mono hstop.measurableSpace_le le_rfl
  have hY : MemLp Y 2 P :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
      X hν τ hstop B hbounded h
  have hYI : Integrable Y P :=
    MeasureTheory.MemLp.integrable
      (show (1 : ENNReal) ≤ 2 by norm_num) hY
  have hb : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K :=
    Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hHbound ω)
  have hHYI : Integrable (fun ω => H ω * Y ω) P :=
    hYI.bdd_mul hHg.aestronglyMeasurable hb
  have hMean :
      (∫ ω, H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c) ∂P) = 0 :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
      X hν τ hτ B hbounded h H hHstop hHg
  change Integrable (fun ω => H ω * Y ω) P ∧
    (∫ ω, H ω * Y ω ∂P) = 0
  exact ⟨hHYI, hMean⟩
