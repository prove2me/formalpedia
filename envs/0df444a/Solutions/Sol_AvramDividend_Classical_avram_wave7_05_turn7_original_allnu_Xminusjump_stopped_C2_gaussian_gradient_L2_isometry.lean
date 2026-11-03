-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:03:46.025893+00:00
-- url     : https://prove2.me/submissions/45929fe6-9b6f-40c4-b477-8b7c08f1bc6b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Actual source X-minus-jumps stopped C2 gradient has L2 isometry and zero expectation. -/
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
    (h : ℝ≥0) (G : Ω → ℝ)
    (hGsource : G = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (BG : ℝ) (hBG : 0 ≤ BG)
    (hGbound : ∀ ω, |G ω| ≤ BG) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : Ω → ℝ := fun ω =>
      M (τ ω + h) ω - M (τ ω) ω
    MemLp (fun ω => G ω * V ω) 2 P ∧
      Integrable (fun ω => G ω * V ω) P ∧
      (∫ ω, G ω * V ω ∂P) = 0 ∧
      (∫ ω, (G ω * V ω) ^ 2 ∂P) =
        ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * G ω ∂P) := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let V : Ω → ℝ := fun ω => M (τ ω + h) ω - M (τ ω) ω
  let W : Ω → ℝ := fun ω =>
    Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c
  have hPred :=
    avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
      X x D hD w C hw q T τ hτ
  dsimp only at hPred
  have hGS :
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G := by
    rw [hGsource]
    exact hPred.1
  have hGglobal : Measurable G := by
    rw [hGsource]
    exact hPred.2.2.1
  have hGrad :=
    avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
      Y hYν τ hτ B hbounded h G hGS hGglobal BG hBG hGbound
  dsimp only at hGrad
  have hVar :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
      Y hYν τ hτ B hbounded h (fun ω => G ω * G ω)
      (hGS.mul hGS) (hGglobal.mul hGglobal)
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
  have hFun : (fun ω => G ω * V ω) =
      (fun ω => G ω * W ω) := by
    funext ω
    rw [hV ω]
  have hSquare : (fun ω => (G ω * V ω) ^ 2) =
      (fun ω => (G ω * G ω) * W ω ^ 2) := by
    funext ω
    rw [hV ω]
    ring
  change MemLp (fun ω => G ω * V ω) 2 P ∧
    Integrable (fun ω => G ω * V ω) P ∧
    (∫ ω, G ω * V ω ∂P) = 0 ∧
    (∫ ω, (G ω * V ω) ^ 2 ∂P) =
      ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * G ω ∂P)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hFun]
    exact hGrad.1
  · rw [hFun]
    exact hGrad.2.1
  · rw [hFun]
    exact hGrad.2.2
  · rw [hSquare]
    rw [hVar, hYσ]
    ring
