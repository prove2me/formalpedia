-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i1r3b_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:03.956242+00:00
-- url     : https://prove2.me/submissions/b114fa34-b655-41c2-95ed-d3e2b2a02b1a

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1_summable_norm_two_geometric
import Theorems.Thm_FourierJacobi_Analysis_i1r3b_reindexed

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)  
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R3BRow => ‖i1Raw t d U V T p.val 0‖) := by
  apply i1r3bEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) (d * T * V * t) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r3b_reindexed t d U V T n)
end FourierJacobi.Analysis
