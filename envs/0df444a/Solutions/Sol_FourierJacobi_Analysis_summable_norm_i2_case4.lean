-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:38.701911+00:00
-- url     : https://prove2.me/submissions/31cd6d35-4b57-4be4-b177-552ebdef8b5d

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case4_reindexed
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
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 7 => ‖i2SpatialTerm q t d U V T 7 p.val‖) := by
  apply i2Case4Equiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 3 * (T * V) ^ 1 * i2DepthMass q 7) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2) hP hE hF using 1
  exact funext fun n => congrArg norm (i2_case4_reindexed q t d U V T n)
end FourierJacobi.Analysis
