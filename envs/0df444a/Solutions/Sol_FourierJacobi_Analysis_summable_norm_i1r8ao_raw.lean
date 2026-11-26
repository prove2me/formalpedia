-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i1r8ao_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:34.313533+00:00
-- url     : https://prove2.me/submissions/9bc837df-d1af-403c-ba12-1b358dcb4781

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1r8ao_reindexed
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_three_geometric


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R8AORow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r8aoEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r8ao_reindexed t d U V T depth n)
end FourierJacobi.Analysis
