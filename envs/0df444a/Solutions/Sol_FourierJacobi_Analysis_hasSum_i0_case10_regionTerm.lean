-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_case10_regionTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:32.957661+00:00
-- url     : https://prove2.me/submissions/5c4dfea3-2a69-4846-8241-2faef621d53b

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i0_lower
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
    (hN : ‖T * V * t / d‖ < 1) (hF : ‖T * U * t ^ 2‖ < 1)
    (hG : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I0LowerRow true => i0Shell t d U V T p.val)
      (Algebra.regionTerms t d (T * U) (T * V) 9) := by
  convert hasSum_i0_lower true t d U V T hN hF hG using 1
  change Algebra.regionTerm9 t d (T * U) (T * V)
    (1 - d * (T * V) * t) (1 - (T * V) * t / d)
    (1 - (T * V) ^ 2 * t ^ 2) (1 - (T * U) * t ^ 2)
    (1 - (T * U) * t ^ 4) = _
  simp only [Algebra.regionTerm9,
    Matrix.cons_val_zero, Matrix.cons_val_succ, i0KInitial, i0KRatio,
    ↓reduceIte, pow_one, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring
end FourierJacobi.Analysis
