-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.intervalIntegrable_partialDeriv_interpWithFill_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:45.790897+00:00
-- url     : https://prove2.me/submissions/d06bd7f2-771c-4236-8922-e7e7080ded75

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_EdgeExtension_partialDeriv_interpWithFill_eq_extension

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution
    (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e)
    (hint : IntervalIntegrable
      (fun t : ℝ => partialDeriv e₀ ρ (F.interpWithFill u t))
      MeasureTheory.volume a b) :
    IntervalIntegrable
      (fun t : ℝ => partialDeriv e₀ ρ
        (F'.interpWithFill (h.extendParam u t) t))
      MeasureTheory.volume a b := by
  refine hint.congr ?_
  intro t ht
  exact h.partialDeriv_interpWithFill_eq_extension u ρ
    (hbound t (Set.uIoc_subset_uIcc ht))
end BKAR.Forest.EdgeExtension
