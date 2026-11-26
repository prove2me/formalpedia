-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case6cc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:10.622405+00:00
-- url     : https://prove2.me/submissions/9dc10fb5-ecb5-44ae-8821-8b511fd67dab

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case6cc_reindexed
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
    (hQ : ‖t ^ 2‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) :
    Summable (fun p : I2SpatialRow 16 => ‖i2SpatialTerm q t d U V T 16 p.val‖) := by
  apply i2Case6ccEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * ((d⁻¹) ^ 2) * t ^ 6 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 16) (T * V * t / d) (t ^ 2) hN hQ using 1
  exact funext fun n => congrArg norm (i2_case6cc_reindexed q t d U V T n)
end FourierJacobi.Analysis
