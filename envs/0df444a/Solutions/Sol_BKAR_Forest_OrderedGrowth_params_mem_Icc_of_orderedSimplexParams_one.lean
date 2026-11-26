-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.params_mem_Icc_of_orderedSimplexParams_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:59.010802+00:00
-- url     : https://prove2.me/submissions/98ea8a8e-13d5-4dc5-aeaf-d58ae83f404b

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_mem_Icc_of_orderedSimplexParams

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    (h : OrderedGrowth F order G) (u : F.EdgeParam → ℝ)
    {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hts : OrderedSimplexParams 1 ts) :
    ∀ e : G.EdgeParam, 0 ≤ h.params u ts e ∧ h.params u ts e ≤ 1 :=
  h.params_mem_Icc_of_orderedSimplexParams u hu le_rfl hts
end BKAR.Forest.OrderedGrowth
