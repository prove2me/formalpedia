-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_case3a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:30:22.622275+00:00
-- url     : https://prove2.me/submissions/41ba956f-d373-49c5-8a9c-9849689b6e47

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2_case3a_reindexed
import Theorems.Thm_FourierJacobi_Analysis_i2_summable_norm_parity_geometric


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
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I2SpatialRow 3 => ‖i2SpatialTerm q t d U V T 3 p.val‖) := by
  apply i2Case3aEquiv.summable_iff.mp
  convert i2_summable_norm_parity_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 3) (T * V * t ^ 2) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2) hP hE hQ using 1
  exact funext fun n => congrArg norm (i2_case3a_reindexed q t d U V T n)
end FourierJacobi.Analysis
