-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i1r5_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:58.751541+00:00
-- url     : https://prove2.me/submissions/6c382311-5a88-44d8-bd8d-2c772da03803

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1r5_reindexed
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
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I1R5Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r5Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) (d * T * V * t) (T * U * t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r5_reindexed t d U V T depth n)
end FourierJacobi.Analysis
