-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i0_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:40.435277+00:00
-- url     : https://prove2.me/submissions/dfb1d994-472d-4659-aea2-e42809b26eec

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0_middle_reindexed
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_three_geometric


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
    Summable (fun p : I0MiddleRow neg => ‖i0Shell t d U V T p.val‖) := by
  apply (i0MiddleRowEquiv neg).summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2))
    (i0KRatio neg t d V T) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2) hK hE hF using 1
  exact funext fun n => congrArg norm (i0_middle_reindexed neg t d U V T n)
end FourierJacobi.Analysis
