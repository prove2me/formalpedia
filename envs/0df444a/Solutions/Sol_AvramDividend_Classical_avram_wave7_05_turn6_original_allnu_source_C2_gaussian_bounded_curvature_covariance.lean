-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_curvature_covariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:56:35.626843+00:00
-- url     : https://prove2.me/submissions/645e4687-b4f1-428f-b4ae-08d74077de45

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Same original source stopped gradient-Hessian Gaussian covariance with the exact
quadratic variation coefficient σ² and automatic predictability and moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGsource : G = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hHsource : H = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hGbound : ∀ ω, |G ω| ≤ BG)
    (hHbound : ∀ ω, |H ω| ≤ BH) :
    let V : Ω → ℝ := fun ω =>
      Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c
    Integrable (fun ω => (G ω * V ω) * (H ω * V ω)) P ∧
    (∫ ω, (G ω * V ω) * (H ω * V ω) ∂P) =
      ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * H ω ∂P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let V : Ω → ℝ := fun ω =>
    Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c
  have hPred :=
    avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
      X x D hD w C hw q T τ hτ
  dsimp only at hPred
  have hGS :
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G := by
    rw [hGsource]
    exact hPred.1
  have hHS :
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H := by
    rw [hHsource]
    exact hPred.2.1
  have hGglobal : Measurable G := by
    rw [hGsource]
    exact hPred.2.2.1
  have hHglobal : Measurable H := by
    rw [hHsource]
    exact hPred.2.2.2
  have hBase :=
    avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
      Y hYν τ hτ B hbounded h G H hGS hHS hGglobal hHglobal
        BG BH hBG hBH hGbound hHbound
  dsimp only at hBase
  have hCellI :
      Integrable (fun ω => (G ω * V ω) * (H ω * V ω)) P :=
    hBase.1
  have hCE :
      P[(fun ω => (G ω * V ω) * (H ω * V ω)) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun ω => ((h : ℝ) * Y.σ ^ 2) * (G ω * H ω)) :=
    hBase.2
  have hIntegralEq :
      (∫ ω, (P[(fun ω => (G ω * V ω) * (H ω * V ω)) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]) ω ∂P) =
        ∫ ω, (G ω * V ω) * (H ω * V ω) ∂P :=
    integral_condExp (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace_le
  change Integrable (fun ω => (G ω * V ω) * (H ω * V ω)) P ∧
    (∫ ω, (G ω * V ω) * (H ω * V ω) ∂P) =
      ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * H ω ∂P)
  refine ⟨hCellI, ?_⟩
  calc
    (∫ ω, (G ω * V ω) * (H ω * V ω) ∂P) =
        ∫ ω, (P[(fun ω => (G ω * V ω) * (H ω * V ω)) |
          (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]) ω ∂P :=
      hIntegralEq.symm
    _ = ∫ ω, ((h : ℝ) * Y.σ ^ 2) * (G ω * H ω) ∂P :=
      integral_congr_ae hCE
    _ = ((h : ℝ) * Y.σ ^ 2) * (∫ ω, G ω * H ω ∂P) := by
      rw [integral_const_mul]
    _ = ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * H ω ∂P) := by
      rw [hYσ]
