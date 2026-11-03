-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn6_original_zerojump_stopped_C2_gradient_auto_L2_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:03:18.622159+00:00
-- url     : https://prove2.me/submissions/ad38f5f5-e1d0-4f3d-a8b9-8abfe376b8f0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Genuine canonical X with zero jump measure: its original stopped C2
controlled-reserve derivative is automatically predictable and gives centred
Gaussian stochastic increments with L2 integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hXν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G : Ω → ℝ)
    (hGsource : G = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K) (hGbound : ∀ ω, |G ω| ≤ K) :
    let V : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    MemLp (fun ω => G ω * V ω) 2 P ∧
    Integrable (fun ω => G ω * V ω) P ∧
    (∫ ω, G ω * V ω ∂P) = 0 := by
  classical
  have hPred :=
    avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
      X x D hD w C hw q T τ hτ
  dsimp only at hPred
  have hGstop :
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G := by
    rw [hGsource]
    exact hPred.1
  have hGglobal : Measurable G := by
    rw [hGsource]
    exact hPred.2.2.1
  have hOne :=
    avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
      X hXν τ hτ B hbounded h G hGstop hGglobal K hK hGbound
  dsimp only at hOne
  exact hOne
