-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegrand_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:10.384217+00:00
-- url     : https://prove2.me/submissions/4bf26188-5d84-4f5d-a335-0add58afbe11

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) :
    h.branchIntegrand u ρ ts =
      mixedPartialList order.reverse ρ (h.branchPoint u ts) :=
  rfl
end BKAR.Forest.OrderedGrowth
