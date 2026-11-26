-- Prove2me | solution 1 for BKAR.BKARContDiff.mixedPartialList_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:05:24.981504+00:00
-- url     : https://prove2.me/submissions/3369da71-b916-45dd-88c1-72b56118df38

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution (hρ : BKARContDiff ρ)
    (es : List (Edge V)) (x : Edge V → ℝ) :
    DifferentiableAt ℝ (BKAR.mixedPartialList es ρ) x :=
  (hρ.mixedPartialList es).differentiableAt x
end BKAR.BKARContDiff
