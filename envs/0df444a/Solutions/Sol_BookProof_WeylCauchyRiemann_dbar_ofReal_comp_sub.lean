-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.dbar_ofReal_comp_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:38.098511+00:00
-- url     : https://prove2.me/submissions/bc246c90-a6f6-4606-869f-5871154a3e49

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.dbar_ofReal_comp_sub
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (z w : ℂ) :
    dbar (fun v => ((χ (z - v) : ℝ) : ℂ)) w = -dbarR χ (z - w) := by

  have hdiff : Differentiable ℝ χ := hχ.differentiable (by simp)
  have h1 : HasFDerivAt (fun v : ℂ => z - v) (-ContinuousLinearMap.id ℝ ℂ) w := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) w).const_sub z
  have h2 : HasFDerivAt χ (fderiv ℝ χ (z - w)) (z - w) := (hdiff (z - w)).hasFDerivAt
  have h3 : HasFDerivAt (fun v : ℂ => ((χ (z - v) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ χ (z - w)).comp (-ContinuousLinearMap.id ℝ ℂ))) w :=
    (Complex.ofRealCLM.hasFDerivAt).comp w (h2.comp w h1)
  rw [dbar, h3.fderiv, dbarR]
  simp
  ring
