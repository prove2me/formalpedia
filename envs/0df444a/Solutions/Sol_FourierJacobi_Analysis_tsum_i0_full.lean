-- Prove2me | solution 1 for FourierJacobi.Analysis.tsum_i0_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:27:05.701727+00:00
-- url     : https://prove2.me/submissions/3e3cd7a2-b1d9-4ffd-ac9d-11e8d3fe0590

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_full

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
    (∑' p : ℤ × ℤ × ℤ, i0Shell t d U V T p) =
      ∑ i : Fin 10, Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide)) :=
  (hasSum_i0_full t d U V T ht hP hN hE hF hG).tsum_eq
end FourierJacobi.Analysis
