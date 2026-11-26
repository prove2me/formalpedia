-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegralAux_cons_eq_integral_tail_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:16.050781+00:00
-- url     : https://prove2.me/submissions/fa3deb79-6c88-40ef-b74f-81187a87152f

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_cons_cons_eq_tail_partialDeriv
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_cons
import Theorems.Thm_BKAR_OrderedSimplexParams_tail
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_congr


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
    (tail : OrderedGrowth F' order G) (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        tail.branchIntegralAux t (step.extendParam u t)
          (partialDeriv e ρ) := by
  rw [branchIntegralAux_cons]
  apply intervalIntegral.integral_congr
  intro t _
  exact orderedSimplexIntegralAux_congr t order
    (fun ts =>
      branchIntegrand_cons_cons_eq_tail_partialDeriv step tail u ρ t ts)
end BKAR.Forest.OrderedGrowth
