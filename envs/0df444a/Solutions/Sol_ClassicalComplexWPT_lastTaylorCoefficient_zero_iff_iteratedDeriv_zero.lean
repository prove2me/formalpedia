-- Prove2me | solution 1 for ClassicalComplexWPT.lastTaylorCoefficient_zero_iff_iteratedDeriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:59:55.791727+00:00
-- url     : https://prove2.me/submissions/9d678b3d-0c1b-4d26-b47d-150ac831a594

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_factorial_smul_lastTaylorCoefficient_zero
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero


attribute [local simp] ClassicalComplexWPT.lastAxis_apply

set_option autoImplicit true
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n k : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (hp : HasFPowerSeriesAt f p 0) :
    lastTaylorCoefficient p k 0 = 0 ↔ iteratedDeriv k (lastSlice f) 0 = 0 := by
  rw [← factorial_smul_lastTaylorCoefficient_zero p hp]
  simp [nsmul_eq_mul, Nat.factorial_ne_zero]
end ClassicalComplexWPT
