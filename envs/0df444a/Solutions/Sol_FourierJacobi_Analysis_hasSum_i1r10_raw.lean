-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1r10_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:49.411492+00:00
-- url     : https://prove2.me/submissions/676902f2-4f75-4efc-8d16-b10494dd1e5c

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1r10_reindexed
import Theorems.Thm_FourierJacobi_Analysis_hasSum_three_geometric


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
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I1R10Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (1 - T * V * t / d)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply i1r10Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) (T * V * t / d) (T * U * t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => i1r10_reindexed t d U V T depth n
end FourierJacobi.Analysis
