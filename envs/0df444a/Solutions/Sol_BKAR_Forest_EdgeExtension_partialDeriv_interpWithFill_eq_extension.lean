-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.partialDeriv_interpWithFill_eq_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:27:14.552141+00:00
-- url     : https://prove2.me/submissions/d544b7d3-a450-42c9-aada-1e96f92a6642

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_EdgeExtension_interpWithFill_extend_eq


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) :
    partialDeriv e₀ ρ (F.interpWithFill u s) =
      partialDeriv e₀ ρ
        (F'.interpWithFill (h.extendParam u s) s) := by
  rw [h.interpWithFill_extend_eq u hu]
end BKAR.Forest.EdgeExtension
