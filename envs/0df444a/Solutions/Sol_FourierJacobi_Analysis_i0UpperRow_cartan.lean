-- Prove2me | solution 1 for FourierJacobi.Analysis.i0UpperRow_cartan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:32.915643+00:00
-- url     : https://prove2.me/submissions/7b0a29ce-39ff-423c-b2a5-3927196ebecd

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Valuations_tableZero_correct
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (neg : Bool) (e : Fin 2) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0UpperRowEquiv neg (e, n)).val.1
      (i0UpperRowEquiv neg (e, n)).val.2.1 (i0UpperRowEquiv neg (e, n)).val.2.2 0 =
      (0, (if neg then (n.1 : ℤ) + 1 else n.1) + 2 * n.2.1 + e.val + 1) := by
  have he := e.isLt
  rw [← tableZero_correct]
  cases neg <;> simp only [i0UpperRowEquiv, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte]
  all_goals unfold tableZero; split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega
end FourierJacobi.Analysis
