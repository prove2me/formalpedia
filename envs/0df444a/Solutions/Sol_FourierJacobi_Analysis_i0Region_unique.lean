-- Prove2me | solution 1 for FourierJacobi.Analysis.i0Region_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:50.926826+00:00
-- url     : https://prove2.me/submissions/1015b3e6-4dbc-4704-bcf4-8b183811931d

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
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
theorem _root_.solution (p : ℤ × ℤ × ℤ) (i j : Fin 10)
    (hi : p ∈ i0Region i) (hj : p ∈ i0Region j) : i = j := by
  fin_cases i <;> fin_cases j <;>
    simp only [i0Region, Matrix.cons_val_zero, Matrix.cons_val_succ, Set.mem_ofPred_eq] at hi hj
  all_goals first | rfl | omega
end FourierJacobi.Analysis
