-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_bounded_hessian_stopped_gaussian_quadratic_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:32:17.418033+00:00
-- url     : https://prove2.me/submissions/ccfc304b-b4c6-4720-9ce8-fb339a2ea8d6

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_controlled_prejump_hessian_stopped_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K) :
    Integrable (fun ω => (stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P := by
  let H : Ω → ℝ := stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hHstopped : Measurable[hstop.measurableSpace] H :=
    avram_wave5_03a_original_controlled_prejump_hessian_stopped_value_measurable
      X x D hD w C hw τ hstop
  have hHg : Measurable H :=
    hHstopped.mono hstop.measurableSpace_le le_rfl
  have hY : MemLp Y 2 P :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
      X hν τ hstop T hbounded h
  have hYsq : Integrable (fun ω => Y ω ^ 2) P :=
    (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mp hY
  have hb : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K :=
    Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hHbound ω)
  change Integrable (fun ω => H ω * (Y ω) ^ 2) P
  exact hYsq.bdd_mul hHg.aestronglyMeasurable hb
