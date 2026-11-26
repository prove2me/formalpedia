-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1r4_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:51.233477+00:00
-- url     : https://prove2.me/submissions/08b53d03-d39a-4dcb-9a17-005a48a2c598

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1r4_reindexed
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
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I1R4Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) := by
  apply i1r4Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r4_reindexed t d U V T depth n
end FourierJacobi.Analysis
