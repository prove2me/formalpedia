-- Prove2me | solution 1 for BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:16.718107+00:00
-- url     : https://prove2.me/submissions/d00e6099-ccef-431f-a50e-24518912d7f2

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
import Theorems.Thm_BKAR_Forest_sum_integrals_activeEdges_eq_sum_activeExtensions

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam, t ≤ u e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b)
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..b,
            mixedPartialList (e.val :: es) ρ
              ((extensions e).forest.interpWithFill
                ((extensions e).extension.extendParam u t) t)) := by
  rw [F.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
    es u ρ b hρ hint]
  rw [F.sum_integrals_activeEdges_eq_sum_activeExtensions
    es u ρ 0 b hbound extensions]
end BKAR.Forest
