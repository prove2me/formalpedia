-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_stopped_quadratic_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:41:23.560996+00:00
-- url     : https://prove2.me/submissions/9610e46e-a4e7-4b8b-b62a-f5ab1ff33277

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Conditional mean zero of original source stopped C2 Hessian Gaussian compensated square. -/
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
    (h : ℝ≥0) (H : Ω → ℝ)
    (hHsource : H = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hHI : Integrable H P)
    (hProdI : Integrable (fun ω =>
      H ω * (Y.X (τ ω + h) ω - Y.X (τ ω) ω -
        (h : ℝ) * Y.c) ^ 2) P) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    P[(fun ω =>
      H ω * (M (τ ω + h) ω - M (τ ω) ω) ^ 2 -
        ((h : ℝ) * X.σ ^ 2) * H ω) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  have hPred :=
    avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
      X x D hD w C hw q T τ hτ
  dsimp only at hPred
  have hHS :
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H := by
    rw [hHsource]
    exact hPred.2.1
  have hOne :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero
      Y hYν τ hτ B hbounded h H hHS hHI hProdI
  have hM : ∀ t : ℝ≥0, ∀ ω : Ω,
      M t ω = Y.X t ω - (t : ℝ) * Y.c := by
    intro t ω
    dsimp [M]
    rw [hSourceDecomp t ω]
    ring
  have hV : ∀ ω : Ω,
      M (τ ω + h) ω - M (τ ω) ω =
        Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c := by
    intro ω
    rw [hM (τ ω + h) ω, hM (τ ω) ω]
    push_cast
    ring
  have hF :
      (fun ω => H ω * (M (τ ω + h) ω - M (τ ω) ω) ^ 2 -
        ((h : ℝ) * X.σ ^ 2) * H ω) =
      (fun ω => H ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c) ^ 2 -
        ((h : ℝ) * Y.σ ^ 2) * H ω) := by
    funext ω
    rw [hV ω, hYσ]
  change
    P[(fun ω => H ω * (M (τ ω + h) ω - M (τ ω) ω) ^ 2 -
      ((h : ℝ) * X.σ ^ 2) * H ω) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))
  rw [hF]
  exact hOne
