-- Prove2me | solution 1 for BKAR.BKARContDiff.mixedPartialList_continuous_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:23:31.8358+00:00
-- url     : https://prove2.me/submissions/29abaaaa-9cd8-4948-a7ed-ed9984dd227f

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
    (es : List (Edge V)) {γ : ℝ → Edge V → ℝ}
    (hγ : Continuous γ) :
    Continuous (fun t : ℝ => BKAR.mixedPartialList es ρ (γ t)) :=
  (hρ.mixedPartialList es).continuous.comp hγ
end BKAR.BKARContDiff
