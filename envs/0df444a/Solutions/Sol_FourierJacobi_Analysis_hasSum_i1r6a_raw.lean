-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1r6a_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:05.535306+00:00
-- url     : https://prove2.me/submissions/b7bc4fcc-25cb-4cf2-a1dd-50a9b88b1986

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1_hasSum_two_geometric
import Theorems.Thm_FourierJacobi_Analysis_i1r6a_reindexed

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖t ^ 2‖ < 1)
    (h1 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R6ARow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r6aEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * V) * t^2) (t ^ 2) (t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r6a_reindexed t d U V T depth n
end FourierJacobi.Analysis
