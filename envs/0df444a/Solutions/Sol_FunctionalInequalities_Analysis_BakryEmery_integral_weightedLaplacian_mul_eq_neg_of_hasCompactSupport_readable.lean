-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:40.793789+00:00
-- url     : https://prove2.me/submissions/e2b25d41-a87b-47a0-839b-8c01a2249e7c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Temperate
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cutoff_eq_one_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_hasCompactSupport_cutoff_readable

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff (R : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) R) := by
    change ContDiff ℝ ∞
      (fun x : E => (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x))
    exact unitBump.contDiff.comp (contDiff_const_smul R⁻¹)
omit [MeasurableSpace E] [BorelSpace E] in
/-- The weighted Laplacian is local: functions agreeing near `x` have the same `ℒ` at `x`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_congr_of_eventuallyEq (V : E → ℝ) {f g : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] g) : weightedLaplacian V f x = weightedLaplacian V g x := by
  rw [weightedLaplacian_apply, weightedLaplacian_apply, h.gradient_eq,
    (InnerProductSpace.laplacian_congr_nhds h).eq_of_nhds]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
/-- Integration by parts against a compactly supported test: `∫ (ℒu) w dμ = -∫ ⟪∇u, ∇w⟫ dμ` for
`u ∈ C²` (no growth condition) and `w ∈ C²` with compact support. -/
theorem solution {V f w : E → ℝ}
    (hV : ContDiff ℝ 1 V) (hf : ContDiff ℝ 2 f) (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x * w x ∂(m.tilted (-V)) =
      -∫ x, ⟪gradient f x, gradient w x⟫ ∂(m.tilted (-V)) := by
    obtain ⟨R₀, hR₀⟩ :=
      hwc.isCompact.isBounded.subset_closedBall (0 : E)
    let R : ℝ := max R₀ 0 + 1
    have hR : 0 < R := by
      dsimp [R]
      positivity
    let F : E → ℝ := fun x => FunctionalInequalities.Analysis.BakryEmery.cutoff R x * f x
    have hF : ContDiff ℝ 2 F := by
      dsimp [F]
      have hc : ContDiff ℝ 2 (FunctionalInequalities.Analysis.BakryEmery.cutoff R) :=
        (FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff (E := E) R).of_le (WithTop.coe_le_coe.mpr le_top)
      exact hc.mul hf
    have hFc : HasCompactSupport F := by
      dsimp [F]
      exact (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_cutoff_readable hR).mul_right
    have h_eq (x : E) (hx : x ∈ tsupport w) :
        f =ᶠ[𝓝 x] F := by
      have hx' : ‖x‖ ≤ max R₀ 0 := by
        have hx'' : x ∈ Metric.closedBall (0 : E) R₀ := hR₀ hx
        have hx''' : ‖x‖ ≤ R₀ := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hx''
        exact hx'''.trans (le_max_left _ _)
      have hxR : x ∈ Metric.ball (0 : E) R := by
        rw [Metric.mem_ball, dist_zero_right]
        dsimp [R]
        linarith
      have hball : Metric.ball (0 : E) R ∈ 𝓝 x :=
        Metric.isOpen_ball.mem_nhds hxR
      filter_upwards [hball] with y hy
      have hy' : ‖y‖ ≤ R := by
        have hy'' : ‖y‖ < R := by
          simpa [Metric.mem_ball, dist_zero_right] using hy
        exact hy''.le
      change f y = FunctionalInequalities.Analysis.BakryEmery.cutoff R y * f y
      rw [FunctionalInequalities.Analysis.BakryEmery.cutoff_eq_one_readable hR hy']
      ring
    have h_lap (x : E) :
        FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x * w x =
          FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V F x * w x := by
      by_cases hx : x ∈ tsupport w
      · have hl :
            FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x = FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V F x :=
          FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_congr_of_eventuallyEq V (h_eq x hx)
        rw [hl]
      · have hwx : w x = 0 :=
          image_eq_zero_of_notMem_tsupport hx
        rw [hwx]
        simp
    have h_grad (x : E) :
        ⟪gradient f x, gradient w x⟫ =
          ⟪gradient F x, gradient w x⟫ := by
      by_cases hx : x ∈ tsupport w
      · exact congrArg (fun z => ⟪z, gradient w x⟫)
          ((h_eq x hx).gradient_eq)
      · have hwx : w =ᶠ[𝓝 x] (fun _ : E => (0 : ℝ)) :=
          notMem_tsupport_iff_eventuallyEq.mp hx
        have hwgrad : gradient w x = 0 := by
          simpa using hwx.gradient_eq
        simp [hwgrad]
    have h₁ :
        (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x * w x ∂(m.tilted (-V))) =
          ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V F x * w x ∂(m.tilted (-V)) := by
      apply integral_congr_ae
      exact ae_of_all _ h_lap
    have h₂ :
        (∫ x, ⟪gradient f x, gradient w x⟫ ∂(m.tilted (-V))) =
          ∫ x, ⟪gradient F x, gradient w x⟫ ∂(m.tilted (-V)) := by
      apply integral_congr_ae
      exact ae_of_all _ h_grad
    have hw1 : ContDiff ℝ 1 w :=
      hw.of_le (show 1 ≤ 2 by norm_num)
    have hIBP :=
      FunctionalInequalities.Analysis.BakryEmery.integral_inner_gradient_tilted m hV hF hFc hw1
    calc
      ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x * w x ∂(m.tilted (-V)) =
          ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V F x * w x ∂(m.tilted (-V)) := h₁
      _ = -∫ x, (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V F x) * w x ∂(m.tilted (-V)) := by
        have hfun :
            (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V F x * w x) =
              (fun x => -((-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V F x) * w x)) := by
          funext x
          ring
        rw [hfun, integral_neg]
      _ = -∫ x, ⟪gradient F x, gradient w x⟫ ∂(m.tilted (-V)) := by
        rw [hIBP]
      _ = -∫ x, ⟪gradient f x, gradient w x⟫ ∂(m.tilted (-V)) := by
        rw [← h₂]
