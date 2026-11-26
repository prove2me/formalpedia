-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case1a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:45.604884+00:00
-- url     : https://prove2.me/submissions/a8075c81-040e-4079-b89f-a7defd32d074

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case1a_reindexed
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_three_geometric


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1) :
    Summable (fun p : I2SpatialRow 0 => ‖i2SpatialTerm q t d U V T 0 p.val‖) := by
  apply i2Case1aEquiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 0) (d * T * V * t) (t ^ 2) (t ^ 2) hP hQ hQ using 1
  exact funext fun n => congrArg norm (i2_case1a_reindexed q t d U V T n)
end FourierJacobi.Analysis
