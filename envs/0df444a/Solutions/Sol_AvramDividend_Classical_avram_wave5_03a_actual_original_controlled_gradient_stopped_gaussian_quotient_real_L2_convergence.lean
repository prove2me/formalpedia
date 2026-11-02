-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_gradient_stopped_gaussian_quotient_real_L2_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:27:13.918976+00:00
-- url     : https://prove2.me/submissions/a5f4fc0a-6f06-4521-877e-4af7f3fecb8b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_controlled_prejump_gradient_stopped_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_quotient_real_L2_convergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Actual controlled prepayment gradient localises same-path exponential quotient convergence in real L2. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K) :
    let G : Ω → ℝ := stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto
      (fun θ : ℝ => (∫ ω, (G ω * (Z θ ω - Y ω)) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let G : Ω → ℝ := stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))
  have hGstop : Measurable[hτ.measurableSpace] G :=
    avram_wave5_03a_original_controlled_prejump_gradient_stopped_value_measurable
      X x D hD w C hw τ hτ
  have hG : StronglyMeasurable G :=
    (hGstop.mono hτ.measurableSpace_le le_rfl).stronglyMeasurable
  change Filter.Tendsto
    (fun θ : ℝ => (∫ ω, (G ω *
      ((Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ -
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c))) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))
  exact
    avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_quotient_real_L2_convergence
      X hν τ hτ T hbounded h G hG K hK hHbound
