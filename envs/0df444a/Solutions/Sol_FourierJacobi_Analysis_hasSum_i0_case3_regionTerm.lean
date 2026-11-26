-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_case3_regionTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:32.224799+00:00
-- url     : https://prove2.me/submissions/04911fc9-08c2-4f37-b59f-99e99fd8d5c5

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_upper
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



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
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I0UpperRow false => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 2) := by
  convert hasSum_i0_upper false t d U V T ht hP hE using 1
  change Algebra.regionTerm2 t d (T * U) (T * V)
    (1 - d * (T * V) * t) (1 - (T * V) * t / d)
    (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
    (1 - (T * U) * t ^ 4) = _
  simp only [Algebra.regionTerm2,
    Matrix.cons_val_zero, Matrix.cons_val_succ, i0KInitial, i0KRatio,
    Bool.false_eq_true, ↓reduceIte, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring
end FourierJacobi.Analysis
