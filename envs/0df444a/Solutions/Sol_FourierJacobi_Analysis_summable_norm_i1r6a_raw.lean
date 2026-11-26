-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i1r6a_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:11.374108+00:00
-- url     : https://prove2.me/submissions/ad768515-4ef8-41bc-a771-f4e1470fd618

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1_summable_norm_two_geometric
import Theorems.Thm_FourierJacobi_Analysis_i1r6a_reindexed

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
    (h0 : ‖t ^ 2‖ < 1)
    (h1 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R6ARow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r6aEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * V) * t^2) (t ^ 2) (t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r6a_reindexed t d U V T depth n)
end FourierJacobi.Analysis
