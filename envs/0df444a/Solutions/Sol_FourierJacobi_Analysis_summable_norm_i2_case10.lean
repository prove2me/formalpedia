-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:12.406882+00:00
-- url     : https://prove2.me/submissions/f4fbc00d-4a8b-44f3-9c9a-56f7538f706a

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case10_reindexed
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
    (hN : ‖T * V * t / d‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 24 => ‖i2SpatialTerm q t d U V T 24 p.val‖) := by
  apply i2Case10Equiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 8 * (T * U) ^ 3 * (T * V) ^ 0 * i2DepthMass q 24) (T * V * t / d) (T * U * t ^ 2) (T * U * t ^ 4) hN hF hG using 1
  exact funext fun n => congrArg norm (i2_case10_reindexed q t d U V T n)
end FourierJacobi.Analysis
