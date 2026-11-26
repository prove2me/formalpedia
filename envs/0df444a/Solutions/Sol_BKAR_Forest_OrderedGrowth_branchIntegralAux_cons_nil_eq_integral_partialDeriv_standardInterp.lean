-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegralAux_cons_nil_eq_integral_partialDeriv_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:42:23.186018+00:00
-- url     : https://prove2.me/submissions/aac5e95d-b172-4d45-b2bf-fdb404cc08f9

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_cons_eq_integral_tail_partialDeriv

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    {F F' : Forest V} {e : Edge V} (step : EdgeExtension F F' e)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step (OrderedGrowth.nil F')).branchIntegralAux top u ρ =
      ∫ t in 0..top, partialDeriv e ρ
        (F'.standardInterp (step.extendParam u t)) := by
  rw [branchIntegralAux_cons_eq_integral_tail_partialDeriv]
  apply intervalIntegral.integral_congr
  intro t _
  rfl
end BKAR.Forest.OrderedGrowth
