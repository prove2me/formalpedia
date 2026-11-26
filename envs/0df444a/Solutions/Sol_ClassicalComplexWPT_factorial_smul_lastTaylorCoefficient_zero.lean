-- Prove2me | solution 1 for ClassicalComplexWPT.factorial_smul_lastTaylorCoefficient_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:19.743383+00:00
-- url     : https://prove2.me/submissions/45ab4e3b-c136-4959-b3fe-8a8da63fda62

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastTaylorCoefficient_zero
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero


attribute [local simp] ClassicalComplexWPT.lastAxis_apply

set_option autoImplicit true
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n k : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (hp : HasFPowerSeriesAt f p 0) :
    k.factorial • lastTaylorCoefficient p k 0 =
      iteratedDeriv k (lastSlice f) 0 := by
  have hpa0 : HasFPowerSeriesAt (fun w : ℂ ↦ f ((0 : Base n), w))
      (p.compContinuousLinearMap (lastAxis n)) 0 := by
    simpa [lastAxis, Function.comp_def] using
      hp.compContinuousLinearMap (u := lastAxis n) (x := (0 : ℂ))
  have hpa : HasFPowerSeriesAt (lastSlice f)
      (p.compContinuousLinearMap (lastAxis n)) 0 := by
    change HasFPowerSeriesAt (fun w : ℂ ↦ f ((0 : Base n), w))
      (p.compContinuousLinearMap (lastAxis n)) 0
    exact hpa0
  have hc := hpa.analyticAt.hasFPowerSeriesAt
  have heq := hpa.eq_formalMultilinearSeries hc
  have hcoeff := congrArg
    (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q k (fun _ ↦ (1 : ℂ))) heq
  have hcoeff' : p k (fun _ ↦ lastDirection n) =
      iteratedDeriv k (lastSlice f) 0 / k.factorial := by
    simpa [lastAxis, lastDirection, FormalMultilinearSeries.compContinuousLinearMap,
      FormalMultilinearSeries.ofScalars] using hcoeff
  rw [lastTaylorCoefficient_zero, hcoeff', nsmul_eq_mul]
  have hfact : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  exact mul_div_cancel₀ _ hfact
end ClassicalComplexWPT
