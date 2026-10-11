-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.dbar_mollify
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:39.364982+00:00
-- url     : https://prove2.me/submissions/cb0adbc4-6651-406b-8b4f-f0ba4e78b0a8

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.dbar_mollify
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_eq_convolution_right
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {F : ℂ → ℂ} (hF : LocallyIntegrable F) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (z : ℂ) :
    dbar (mollify F χ) z = ∫ w : ℂ, dbarR χ (z - w) * F w := by

  set L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip with hLdef
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  have hfd : HasFDerivAt (mollify F χ) ((F ⋆[L.precompR ℂ, volume] fderiv ℝ χ) z) z := by
    rw [mollify_eq_convolution_right]
    exact hχc.hasFDerivAt_convolution_right L hF hχ1 z
  have hcfd : HasCompactSupport (fderiv ℝ χ) := hχc.fderiv ℝ
  have hcontfd : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by simp)
  have happ : ∀ v : ℂ, fderiv ℝ (mollify F χ) z v
      = ∫ w : ℂ, ((fderiv ℝ χ (z - w) v : ℝ) : ℂ) * F w := by
    intro v
    rw [hfd.fderiv, convolution_precompR_apply L hF hcfd hcontfd z v]
    simp [convolution_def, hLdef, Complex.real_smul]
  have hint : ∀ v : ℂ, Integrable (fun w : ℂ => ((fderiv ℝ χ (z - w) v : ℝ) : ℂ) * F w) := by
    intro v
    have hcs : HasCompactSupport (fun a : ℂ => (fderiv ℝ χ a v : ℝ)) :=
      hcfd.comp_left (g := fun T : ℂ →L[ℝ] ℝ => T v) (by simp)
    have hcont : Continuous (fun a : ℂ => (fderiv ℝ χ a v : ℝ)) :=
      hcontfd.clm_apply continuous_const
    have hthis := hcs.convolutionExists_right L hF hcont z
    rw [ConvolutionExistsAt] at hthis
    simpa [hLdef, Complex.real_smul] using hthis
  rw [dbar, happ 1, happ Complex.I, ← MeasureTheory.integral_const_mul,
    ← integral_add (hint 1) ((hint Complex.I).const_mul _)]
  congr 1
  funext w
  simp only [dbarR]
  ring
