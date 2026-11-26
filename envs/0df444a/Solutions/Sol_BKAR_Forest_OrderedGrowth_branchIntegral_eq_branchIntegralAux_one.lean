-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegral_eq_branchIntegralAux_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:09.839221+00:00
-- url     : https://prove2.me/submissions/e37223d5-5a7b-4b86-b972-46be4ccf7b0f

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    h.branchIntegral u ρ = h.branchIntegralAux 1 u ρ :=
  rfl
end BKAR.Forest.OrderedGrowth
