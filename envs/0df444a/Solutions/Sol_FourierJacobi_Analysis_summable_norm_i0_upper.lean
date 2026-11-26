-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i0_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:49.610144+00:00
-- url     : https://prove2.me/submissions/0172f65f-530b-4fea-bb8e-c04eca5c0bb9

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_upper_reindexed

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (neg : Bool) (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I0UpperRow neg => ‖i0Shell t d U V T p.val‖) :=
  (i0UpperRowEquiv neg).summable_iff.mp
    (summable_norm_i0_upper_reindexed neg t d U V T ht hK hE)
end FourierJacobi.Analysis
