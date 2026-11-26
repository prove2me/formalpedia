-- Prove2me | solution 1 for BKAR.Forest.sum_integrals_activeEdges_mixedPartialList_eq_zero_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:33.204786+00:00
-- url     : https://prove2.me/submissions/5690b52b-7685-4ca0-a521-4fd7fb555798

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ) (hF : F.activeEdges = ∅) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        mixedPartialList (e :: es) ρ (F.interpWithFill u t)) = 0 := by
  rw [hF]
  exact Finset.sum_empty
end BKAR.Forest
