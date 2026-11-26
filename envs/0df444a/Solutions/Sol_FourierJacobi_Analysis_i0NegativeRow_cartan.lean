-- Prove2me | solution 1 for FourierJacobi.Analysis.i0NegativeRow_cartan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:35.775779+00:00
-- url     : https://prove2.me/submissions/f2224f1a-ee58-48da-a87f-40f2f1952242

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Valuations_tableZero_correct

attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (tail : Bool) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0NegativeRowEquiv tail n).val.1
      (i0NegativeRowEquiv tail n).val.2.1
      (i0NegativeRowEquiv tail n).val.2.2 0 =
      (if tail then (2 * (n.2.2 : ℤ) + 2, (n.1 : ℤ) + 1)
        else (0, (n.1 : ℤ) + 1)) := by
  rw [← tableZero_correct]
  have hk : ¬ 0 ≤ -(n.1 : ℤ) - 1 := by omega
  have hj : 0 ≤ (n.2.1 : ℤ) := by omega
  cases tail
  · change tableZero (-(n.1 : ℤ) - 1) (n.2.1 : ℤ) (n.2.2 : ℤ) =
      (0, (n.1 : ℤ) + 1)
    have hh : 0 ≤ (n.2.2 : ℤ) := by omega
    rw [tableZero, if_neg hk, if_pos hj, if_pos hh]
    simp only [Prod.mk.injEq]
    exact ⟨trivial, by ring⟩
  · change tableZero (-(n.1 : ℤ) - 1) (n.2.1 : ℤ) (-(n.2.2 : ℤ) - 1) =
      (2 * (n.2.2 : ℤ) + 2, (n.1 : ℤ) + 1)
    have hh : ¬ 0 ≤ -(n.2.2 : ℤ) - 1 := by omega
    rw [tableZero, if_neg hk, if_pos hj, if_neg hh]
    simp only [Prod.mk.injEq]
    omega
end FourierJacobi.Analysis
