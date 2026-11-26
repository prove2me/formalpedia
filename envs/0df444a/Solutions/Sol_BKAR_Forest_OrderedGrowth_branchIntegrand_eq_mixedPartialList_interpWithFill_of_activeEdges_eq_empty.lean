-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:03.96466+00:00
-- url     : https://prove2.me/submissions/ce5d732b-b8a9-42a5-bef3-2c5d6f6eb600

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_eq_interpWithFill_of_activeEdges_eq_empty

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    (h : OrderedGrowth F order G) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) (b : ℝ)
    (hG : G.activeEdges = ∅) :
    h.branchIntegrand u ρ ts =
      mixedPartialList h.derivativeOrder ρ
        (G.interpWithFill (h.params u ts) b) := by
  change mixedPartialList h.derivativeOrder ρ (h.branchPoint u ts) =
    mixedPartialList h.derivativeOrder ρ
      (G.interpWithFill (h.params u ts) b)
  rw [h.branchPoint_eq_interpWithFill_of_activeEdges_eq_empty u ts b hG]
end BKAR.Forest.OrderedGrowth
