-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegralAux_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:14.678201+00:00
-- url     : https://prove2.me/submissions/724b6c20-64e4-4dbe-aa94-a426c413c85c

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
theorem _root_.solution (top : ℝ) (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.nil F).branchIntegralAux top u ρ = ρ (F.standardInterp u) :=
  rfl
end BKAR.Forest.OrderedGrowth
