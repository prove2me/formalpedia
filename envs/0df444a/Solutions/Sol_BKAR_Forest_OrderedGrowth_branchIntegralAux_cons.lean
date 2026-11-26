-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegralAux_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:33.850083+00:00
-- url     : https://prove2.me/submissions/fed439f6-e696-46bf-acc5-9dbb7c420762

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        orderedSimplexIntegralAux t order
          (fun ts =>
            (OrderedGrowth.cons step tail).branchIntegrand u ρ (t :: ts)) :=
  rfl
end BKAR.Forest.OrderedGrowth
