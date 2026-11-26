-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.integral_partialDeriv_interpWithFill_eq_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:49.766802+00:00
-- url     : https://prove2.me/submissions/194c07db-6e33-4204-adc3-1142fbe07653

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
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e) :
    (∫ t in a..b, partialDeriv e₀ ρ (F.interpWithFill u t)) =
      ∫ t in a..b, partialDeriv e₀ ρ
        (F'.interpWithFill (h.extendParam u t) t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact h.partialDeriv_interpWithFill_eq_extension u ρ (hbound t ht)
end BKAR.Forest.EdgeExtension
