-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case6bb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:33:20.88954+00:00
-- url     : https://prove2.me/submissions/9903fcb5-9fe3-4edb-a31f-ff1c38be04f7

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case6bb_reindexed
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
    (hQ : ‖t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 13 => ‖i2SpatialTerm q t d U V T 13 p.val‖) := by
  apply i2Case6bbEquiv.summable_iff.mp
  convert i2_summable_norm_one_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 13) (t ^ 2) hQ using 1
  exact funext fun n => congrArg norm (i2_case6bb_reindexed q t d U V T n)
end FourierJacobi.Analysis
