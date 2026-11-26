-- Prove2me | solution 1 for BKAR.BKARContDiff.mixedPartialList_intervalIntegrable_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:29.555169+00:00
-- url     : https://prove2.me/submissions/57d44e49-ce3b-4f04-bd4f-6d2360e332c4

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_continuous_comp

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution (hρ : BKARContDiff ρ)
    (es : List (Edge V)) {γ : ℝ → Edge V → ℝ}
    (hγ : Continuous γ) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => BKAR.mixedPartialList es ρ (γ t))
      MeasureTheory.volume a b :=
  (hρ.mixedPartialList_continuous_comp es hγ).intervalIntegrable a b
end BKAR.BKARContDiff
