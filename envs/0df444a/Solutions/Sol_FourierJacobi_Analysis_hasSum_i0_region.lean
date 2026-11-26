-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:19.270815+00:00
-- url     : https://prove2.me/submissions/1bd3cad7-f9c4-4269-a1b5-11b7b4903872

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case3_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case4_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case5_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case8_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case9_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case10_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case1_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case2_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case6_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case7_regionTerm


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
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) (i : Fin 10) :
    HasSum (fun p : i0Region i => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide))) := by
  fin_cases i
  · exact hasSum_i0_case1_regionTerm t d U V T ht hP
  · exact hasSum_i0_case2_regionTerm t d U V T ht hP hG
  · exact hasSum_i0_case3_regionTerm t d U V T ht hP hE
  · exact hasSum_i0_case4_regionTerm t d U V T hP hE hF
  · exact hasSum_i0_case5_regionTerm t d U V T hP hF hG
  · exact hasSum_i0_case6_regionTerm t d U V T ht hN
  · exact hasSum_i0_case7_regionTerm t d U V T ht hN hG
  · exact hasSum_i0_case8_regionTerm t d U V T ht hN hE
  · exact hasSum_i0_case9_regionTerm t d U V T hN hE hF
  · exact hasSum_i0_case10_regionTerm t d U V T hN hF hG
end FourierJacobi.Analysis
