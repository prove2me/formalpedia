-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:37.94067+00:00
-- url     : https://prove2.me/submissions/e9cdb071-2ace-40d1-b6bf-1d2782fdfb96

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0_middle_reindexed
import Theorems.Thm_FourierJacobi_Analysis_hasSum_three_geometric


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (neg : Bool) (t d U V T : ℂ)
    (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) (hF : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I0MiddleRow neg => i0Shell t d U V T p.val)
      (((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2)) *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ *
        (1 - T * U * t ^ 2)⁻¹) := by
  apply (i0MiddleRowEquiv neg).hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2))
    (i0KRatio neg t d V T) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2) hK hE hF using 1
  exact funext fun n => i0_middle_reindexed neg t d U V T n
end FourierJacobi.Analysis
