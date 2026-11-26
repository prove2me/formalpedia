-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_case1_regionTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:07.220088+00:00
-- url     : https://prove2.me/submissions/05bcd896-85a5-48eb-9914-ec7d43fb517a

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_case1
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1) :
    HasSum (fun p : I0PositiveRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerm0 t d (T * U) (T * V)
        (1 - d * (T * V) * t) (1 - (T * V) * t / d)
        (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
        (1 - (T * U) * t ^ 4)) := by
  simpa only [Algebra.regionTerm0, pow_one, mul_assoc]
    using hasSum_i0_case1 t d U V T ht hP
end FourierJacobi.Analysis
