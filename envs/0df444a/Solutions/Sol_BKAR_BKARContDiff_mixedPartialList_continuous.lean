-- Prove2me | solution 1 for BKAR.BKARContDiff.mixedPartialList_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:56:20.76455+00:00
-- url     : https://prove2.me/submissions/16a45f50-56ad-45cf-8e6f-d60b3ed6cc72

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_BKARContDiff_continuous

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution (hρ : BKARContDiff ρ)
    (es : List (Edge V)) :
    Continuous (BKAR.mixedPartialList es ρ) :=
  (hρ.mixedPartialList es).continuous
end BKAR.BKARContDiff
