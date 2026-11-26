-- Prove2me | solution 1 for BKAR.BKARContDiff.mixedPartialList_standardInterp_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:26.334849+00:00
-- url     : https://prove2.me/submissions/25de6c83-98e5-4a1f-8478-88f6bde77674

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_intervalIntegrable_comp
import Theorems.Thm_BKAR_Forest_standardInterp_continuous_comp

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR
namespace BKARContDiff
theorem _root_.solution
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (F : Forest V) {uPath : ℝ → F.EdgeParam → ℝ}
    (hu : Continuous uPath) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => BKAR.mixedPartialList es ρ
        (F.standardInterp (uPath t)))
      MeasureTheory.volume a b :=
  hρ.mixedPartialList_intervalIntegrable_comp es
    (F.standardInterp_continuous_comp hu) a b
end BKARContDiff
end BKAR
