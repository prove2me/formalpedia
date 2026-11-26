-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_case6_regionTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:29.039184+00:00
-- url     : https://prove2.me/submissions/b2e35b3f-31b6-4da3-8fa9-d4f38e5313f0

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case6
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hN : ‖T * V * t / d‖ < 1) :
    HasSum (fun p : I0NegativeRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerm5 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by
  convert hasSum_i0_case6 t d U V T ht hN using 1
  simp only [Algebra.regionTerm5, pow_one, div_eq_mul_inv, mul_assoc]
  ring
end FourierJacobi.Analysis
