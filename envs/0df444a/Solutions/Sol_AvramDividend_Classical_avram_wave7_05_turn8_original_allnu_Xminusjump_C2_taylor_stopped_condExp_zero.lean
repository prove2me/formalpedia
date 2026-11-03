-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn8_original_allnu_Xminusjump_C2_taylor_stopped_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:47:09.067006+00:00
-- url     : https://prove2.me/submissions/ad3f470a-69f5-47d9-8b36-7524b9756dc2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Exact source stopped C2 Gaussian half-square Taylor residual has conditional mean zero. -/
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
    (hGI : Integrable (fun ω => G ω *
      (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) P)
    (hHI : Integrable H P)
    (hH2I : Integrable (fun ω => H ω *
      (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c) ^ 2) P) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : Ω → ℝ := fun ω => M (τ ω + h) ω - M (τ ω) ω
    let R : Ω → ℝ := fun ω =>
      G ω * V ω + (1 / 2 : ℝ) * H ω *
        (V ω ^ 2 - (h : ℝ) * X.σ ^ 2)
    Integrable R P ∧
      P[R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let V : Ω → ℝ := fun ω => M (τ ω + h) ω - M (τ ω) ω
  let W : Ω → ℝ := fun ω =>
    Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c
  let R : Ω → ℝ := fun ω =>
    G ω * V ω + (1 / 2 : ℝ) * H ω *
      (V ω ^ 2 - (h : ℝ) * X.σ ^ 2)
  let S : Ω → ℝ := fun ω =>
    G ω * W ω + (((1 / 2 : ℝ) * H ω) * W ω ^ 2 -
      ((h : ℝ) * Y.σ ^ 2) * ((1 / 2 : ℝ) * H ω))
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
  have hHS' :
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        (fun ω => (1 / 2 : ℝ) * H ω) :=
    measurable_const.mul hHS
  have hHI' : Integrable (fun ω => (1 / 2 : ℝ) * H ω) P :=
    hHI.const_mul _
  have hH2I' : Integrable (fun ω =>
      ((1 / 2 : ℝ) * H ω) * W ω ^ 2) P := by
    have hEq : (fun ω => ((1 / 2 : ℝ) * H ω) * W ω ^ 2) =
        (fun ω => (1 / 2 : ℝ) * (H ω * W ω ^ 2)) := by
      funext ω
      ring
    rw [hEq]
    exact hH2I.const_mul _
  have hOne :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
      Y hYν τ hτ B hbounded h G (fun ω => (1 / 2 : ℝ) * H ω)
      hGS hHS' hGI hHI' hH2I'
  dsimp only at hOne
  have hM : ∀ t : ℝ≥0, ∀ ω : Ω,
      M t ω = Y.X t ω - (t : ℝ) * Y.c := by
    intro t ω
    dsimp [M]
    rw [hSourceDecomp t ω]
    ring
  have hV : ∀ ω : Ω, V ω = W ω := by
    intro ω
    dsimp [V, W]
    rw [hM (τ ω + h) ω, hM (τ ω) ω]
    push_cast
    ring
  have hRS : R = S := by
    funext ω
    dsimp [R, S]
    rw [hV ω, hYσ]
    ring
  have hShape :
      Integrable S P ∧
        P[S | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
          =ᵐ[P] (fun _ => (0 : ℝ)) := by
    exact hOne
  change Integrable R P ∧
    P[R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))
  rw [hRS]
  exact hShape
