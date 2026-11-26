-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegrand_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:36.050506+00:00
-- url     : https://prove2.me/submissions/6447e241-cfe2-4f47-bc00-f28c1590a688

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
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) :
    (OrderedGrowth.nil F).branchIntegrand u ρ ts = ρ (F.standardInterp u) :=
  rfl
end BKAR.Forest.OrderedGrowth
