-- Prove2me | solution 1 for BKAR.BKARContDiff.mixedPartialList_interpWithFill_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:31.080583+00:00
-- url     : https://prove2.me/submissions/354df24b-e027-4bf8-8fcf-f7aa62d0a9e0

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_intervalIntegrable_comp
import Theorems.Thm_BKAR_Forest_interpWithFill_continuous

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR
namespace BKARContDiff
theorem _root_.solution
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (F : Forest V) (u : F.EdgeParam → ℝ) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => BKAR.mixedPartialList es ρ
        (F.interpWithFill u t))
      MeasureTheory.volume a b :=
  hρ.mixedPartialList_intervalIntegrable_comp es
    (F.interpWithFill_continuous u) a b
end BKARContDiff
end BKAR
