-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegral_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:47.275825+00:00
-- url     : https://prove2.me/submissions/2366c638-51c3-4e41-bf71-76802db725ab

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
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.nil F).branchIntegral u ρ = ρ (F.standardInterp u) :=
  rfl
end BKAR.Forest.OrderedGrowth
