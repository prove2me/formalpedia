-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1r8b_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:28:19.37349+00:00
-- url     : https://prove2.me/submissions/e2a442b1-cfc2-4b80-9233-d31430f07e34

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1_hasSum_two_geometric
import Theorems.Thm_FourierJacobi_Analysis_i1r8b_reindexed

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)  
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I1R8BRow => i1Raw t d U V T p.val 0)
      (((1 - t ^ 2) ^ 3 * (T * U)) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  apply i1r8bEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)) (T * V * t / d) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r8b_reindexed t d U V T n
end FourierJacobi.Analysis
