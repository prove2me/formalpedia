-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:30.102035+00:00
-- url     : https://prove2.me/submissions/d024b133-189b-498f-8f13-71d4025869ef

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0Region_partition
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_region
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_full

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : ℤ × ℤ × ℤ => i0Shell t d U V T p)
      (∑ i : Fin 10, Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide))) := by
  let e := Set.sigmaEquiv i0Region i0Region_partition
  have hs := (summable_norm_i0_full t d U V T ht hP hN hE hF hG).of_norm
  have hs' : Summable (fun p : Σ i : Fin 10, i0Region i => i0Shell t d U V T p.2.val) :=
    e.summable_iff.mpr hs
  apply e.hasSum_iff.mp
  exact (hasSum_fintype _).sigma_of_hasSum
    (hasSum_i0_region t d U V T ht hP hN hE hF hG) hs'
end FourierJacobi.Analysis
