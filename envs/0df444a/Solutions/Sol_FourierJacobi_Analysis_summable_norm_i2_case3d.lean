-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case3d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:11.539975+00:00
-- url     : https://prove2.me/submissions/7b6b7bac-4ca6-4a7e-9968-1a2eeb5b3eba

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case3d_reindexed
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
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 6 => ‖i2SpatialTerm q t d U V T 6 p.val‖) := by
  apply i2Case3dEquiv.summable_iff.mp
  convert i2_summable_norm_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 1 * (T * U) ^ 0 * (T * V) ^ 3 * i2DepthMass q 6) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) hP hE using 1
  exact funext fun n => congrArg norm (i2_case3d_reindexed q t d U V T n)
end FourierJacobi.Analysis
