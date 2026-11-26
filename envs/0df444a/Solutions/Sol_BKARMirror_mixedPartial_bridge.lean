-- Prove2me | solution 1 for BKARMirror.mixedPartial_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:09.009224+00:00
-- url     : https://prove2.me/submissions/81c24565-7b2a-4f51-9114-d56fbcbb02cc

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
import Theorems.Thm_BKARMirror_mixedPartialList_bridge

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKARMirror
theorem _root_.solution (J : ForestIndex V)
    (data : BKAR.AcyclicEdgeSetData J.edges) (ρ : (Edge V → ℝ) → ℝ) :
    mixedPartial J ρ = (data.toForest).mixedPartial ρ :=
  mixedPartialList_bridge J.edges.toList ρ
end BKARMirror
