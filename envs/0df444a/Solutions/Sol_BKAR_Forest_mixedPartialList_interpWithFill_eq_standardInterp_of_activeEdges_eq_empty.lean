-- Prove2me | solution 1 for BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:05.613294+00:00
-- url     : https://prove2.me/submissions/b7149fdc-b10e-4530-b2f9-534e9a874cdf

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) (hF : F.activeEdges = ∅) :
    mixedPartialList es ρ (F.interpWithFill u t) =
      mixedPartialList es ρ (F.standardInterp u) := by
  rw [F.interpWithFill_eq_standardInterp_of_activeEdges_eq_empty u t hF]
end BKAR.Forest
