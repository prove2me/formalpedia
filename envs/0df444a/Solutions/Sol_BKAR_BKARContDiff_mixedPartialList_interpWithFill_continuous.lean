-- Prove2me | solution 1 for BKAR.BKARContDiff.mixedPartialList_interpWithFill_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:41.4664+00:00
-- url     : https://prove2.me/submissions/8cb234e1-181a-4a09-b875-50a33ddd55bc

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_continuous_comp
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
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    Continuous
      (fun t : ℝ => BKAR.mixedPartialList es ρ
        (F.interpWithFill u t)) :=
  hρ.mixedPartialList_continuous_comp es (F.interpWithFill_continuous u)
end BKARContDiff
end BKAR
