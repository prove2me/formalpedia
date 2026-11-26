-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case6bbb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:33:23.805065+00:00
-- url     : https://prove2.me/submissions/0db039cd-6346-4ee4-941b-d272d60469a4

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case6bbb_reindexed
import Theorems.Thm_FourierJacobi_Analysis_i2_summable_norm_one_geometric


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
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 14 => ‖i2SpatialTerm q t d U V T 14 p.val‖) := by
  apply i2Case6bbbEquiv.summable_iff.mp
  convert i2_summable_norm_one_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 7 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 14) (T * U * t ^ 4) hG using 1
  exact funext fun n => congrArg norm (i2_case6bbb_reindexed q t d U V T n)
end FourierJacobi.Analysis
