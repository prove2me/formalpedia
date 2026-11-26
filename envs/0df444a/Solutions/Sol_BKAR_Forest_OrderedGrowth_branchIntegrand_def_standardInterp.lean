-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegrand_def_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:23.219905+00:00
-- url     : https://prove2.me/submissions/47cd9ed1-bfb0-4e1d-ad8c-15fef9dc14c0

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
      mixedPartialList order.reverse ρ (G.standardInterp (h.params u ts)) :=
  rfl
end BKAR.Forest.OrderedGrowth
