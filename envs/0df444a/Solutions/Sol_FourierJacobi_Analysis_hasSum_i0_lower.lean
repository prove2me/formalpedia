-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:44.831797+00:00
-- url     : https://prove2.me/submissions/d4674b8a-005a-4328-8bba-2ad568079398

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0_lower_reindexed
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
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0LowerRow neg => i0Shell t d U V T p.val)
      (((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2) * (T * U * t ^ 4)) *
        (1 - i0KRatio neg t d V T)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply (i0LowerRowEquiv neg).hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2) * (T * U * t ^ 4))
    (i0KRatio neg t d V T) (T * U * t ^ 2) (T * U * t ^ 4) hK hF hG using 1
  exact funext fun n => i0_lower_reindexed neg t d U V T n
end FourierJacobi.Analysis
