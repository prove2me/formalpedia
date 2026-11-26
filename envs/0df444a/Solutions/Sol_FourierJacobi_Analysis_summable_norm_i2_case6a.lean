-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case6a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:13.596073+00:00
-- url     : https://prove2.me/submissions/67c7eee0-c9ff-46c2-8970-fe0fdcdefacd

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case6a_reindexed
import Theorems.Thm_FourierJacobi_Analysis_i2_summable_norm_two_geometric


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
    Summable (fun p : I2SpatialRow 9 => ‖i2SpatialTerm q t d U V T 9 p.val‖) := by
  apply i2Case6aEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 0) * t ^ 6 * (T * U) ^ 0 * (T * V) ^ 2 * i2DepthMass q 9) (t ^ 2) (t ^ 2) hQ hQ using 1
  exact funext fun n => congrArg norm (i2_case6a_reindexed q t d U V T n)
end FourierJacobi.Analysis
