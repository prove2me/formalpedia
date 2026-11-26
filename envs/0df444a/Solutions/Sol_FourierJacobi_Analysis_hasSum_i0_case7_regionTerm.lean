-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_case7_regionTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:30.843385+00:00
-- url     : https://prove2.me/submissions/96acd848-d883-423b-bf4d-814743ea4704

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case7
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0NegativeRow true => i0Shell t d U V T p.val)
      (Algebra.regionTerm6 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by
  convert hasSum_i0_case7 t d U V T ht hN hG using 1
  simp only [Algebra.regionTerm6, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring
end FourierJacobi.Analysis
