-- Prove2me | solution 1 for BKAR.Forest.integral_activeEdgePartialSum_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:07.66487+00:00
-- url     : https://prove2.me/submissions/5d2d5d64-9142-4e23-9dac-e3cd9032ea22

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_hasDerivAt_rho_interpWithFill_of_differentiableAt


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ρ (F.interpWithFill u t))
    (hint : IntervalIntegrable (fun t : ℝ => F.activeEdgePartialSum u ρ t)
      MeasureTheory.volume a b) :
    (∫ t in a..b, F.activeEdgePartialSum u ρ t) =
      ρ (F.interpWithFill u b) - ρ (F.interpWithFill u a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht =>
      F.hasDerivAt_rho_interpWithFill_of_differentiableAt u (hρ t ht))
    hint
end BKAR.Forest
