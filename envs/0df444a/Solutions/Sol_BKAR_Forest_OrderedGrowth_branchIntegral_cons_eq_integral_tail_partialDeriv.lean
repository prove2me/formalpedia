-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegral_cons_eq_integral_tail_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:33.95116+00:00
-- url     : https://prove2.me/submissions/9674454c-6f4d-4a60-80f6-880e1e951687

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_cons_eq_integral_tail_partialDeriv
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    {F F' G : Forest V} {e : Edge V} {order : List (Edge V)}
    (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (step.extendParam u t)
          (partialDeriv e ρ) :=
  (OrderedGrowth.branchIntegralAux_cons_eq_integral_tail_partialDeriv
    step tail 1 u ρ)
end BKAR.Forest.OrderedGrowth
