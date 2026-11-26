-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.mixedPartialList_cons_interpWithFill_eq_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:20:18.236303+00:00
-- url     : https://prove2.me/submissions/c3dd0f2a-bd7e-407a-a212-384cb7f57ed0

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_EdgeExtension_partialDeriv_interpWithFill_eq_extension
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_cons_apply



set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution
    (h : EdgeExtension F F' e₀)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) :
    partialDeriv e₀ (mixedPartialList es ρ) (F.interpWithFill u s) =
      mixedPartialList (e₀ :: es) ρ
        (F'.interpWithFill (h.extendParam u s) s) := by
  rw [mixedPartialList_cons_apply]
  exact h.partialDeriv_interpWithFill_eq_extension u
    (mixedPartialList es ρ) hu
end BKAR.Forest.EdgeExtension
