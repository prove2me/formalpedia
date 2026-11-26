-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case6ccc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:19.098988+00:00
-- url     : https://prove2.me/submissions/914563d0-3be5-49ca-971d-ca82df443cbb

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case6ccc_reindexed
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
    (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I2SpatialRow 17 => ‖i2SpatialTerm q t d U V T 17 p.val‖) := by
  apply i2Case6cccEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 8 * (T * U) ^ 2 * (T * V) ^ 2 * i2DepthMass q 17) (T * V * t / d) (T * U * t ^ 4) hN hG using 1
  exact funext fun n => congrArg norm (i2_case6ccc_reindexed q t d U V T n)
end FourierJacobi.Analysis
