-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.params_mem_Icc_of_orderedSimplexParams
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:58.359845+00:00
-- url     : https://prove2.me/submissions/03473274-0b4f-43a9-9446-4619d90ef62c

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_mem_Icc
import Theorems.Thm_BKAR_OrderedSimplexParams_le_top_of_mem
import Theorems.Thm_BKAR_OrderedSimplexParams_nonneg_of_mem


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) {top : ℝ} {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (htop : top ≤ 1) (hts : OrderedSimplexParams top ts) :
    ∀ e : G.EdgeParam, 0 ≤ h.params u ts e ∧ h.params u ts e ≤ 1 :=
  h.params_mem_Icc u ts hu (fun _ ht =>
    ⟨OrderedSimplexParams.nonneg_of_mem hts ht,
      (OrderedSimplexParams.le_top_of_mem hts ht).trans htop⟩)
end BKAR.Forest.OrderedGrowth
