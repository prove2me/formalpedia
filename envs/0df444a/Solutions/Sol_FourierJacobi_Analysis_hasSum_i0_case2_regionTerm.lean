-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_case2_regionTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:12.525184+00:00
-- url     : https://prove2.me/submissions/1887b032-4c32-4117-ba1e-babe4ac49f7e

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case2
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0PositiveRow true => i0Shell t d U V T p.val)
      (Algebra.regionTerm1 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by
  convert hasSum_i0_case2 t d U V T ht hP hG using 1
  simp only [Algebra.regionTerm1, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring
end FourierJacobi.Analysis
