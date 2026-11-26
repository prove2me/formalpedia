-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:38.138979+00:00
-- url     : https://prove2.me/submissions/b8f22dc8-1b7c-4a02-8d61-17cf80ead6ad

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case7_reindexed
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
    (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 18 => ‖i2SpatialTerm q t d U V T 18 p.val‖) := by
  apply i2Case7Equiv.summable_iff.mp
  convert summable_norm_three_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 5 * (T * U) ^ 1 * (T * V) ^ 1 * i2DepthMass q 18) (T * V * t / d) (t ^ 2) (T * U * t ^ 4) hN hQ hG using 1
  exact funext fun n => congrArg norm (i2_case7_reindexed q t d U V T n)
end FourierJacobi.Analysis
