-- Prove2me | solution 1 for FourierJacobi.Analysis.i0PositiveRow_cartan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:17.142713+00:00
-- url     : https://prove2.me/submissions/6dfe2406-bbec-4ade-882a-c7cf05cdeaf2

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Valuations_tableZero_correct


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (tail : Bool) (n : ℕ × ℕ × ℕ) :
    cartanIndices 0 (i0PositiveRowEquiv tail n).val.1
      (i0PositiveRowEquiv tail n).val.2.1
      (i0PositiveRowEquiv tail n).val.2.2 0 =
      (if tail then (2 * (n.2.2 : ℤ) + 2, (n.1 : ℤ)) else (0, (n.1 : ℤ))) := by
  rw [← tableZero_correct]
  have hk : 0 ≤ (n.1 : ℤ) := by omega
  have hj : -2 * (n.1 : ℤ) ≤ (n.2.1 : ℤ) - 2 * n.1 := by omega
  cases tail
  · change tableZero (n.1 : ℤ) ((n.2.1 : ℤ) - 2 * n.1)
      ((n.2.2 : ℤ) - n.1) = (0, (n.1 : ℤ))
    have hh : -(n.1 : ℤ) ≤ (n.2.2 : ℤ) - n.1 := by omega
    rw [tableZero, if_pos hk, if_pos hj, if_pos hh]
  · change tableZero (n.1 : ℤ) ((n.2.1 : ℤ) - 2 * n.1)
      (-(n.1 : ℤ) - n.2.2 - 1) = (2 * (n.2.2 : ℤ) + 2, (n.1 : ℤ))
    have hh : ¬ -(n.1 : ℤ) ≤ -(n.1 : ℤ) - n.2.2 - 1 := by omega
    rw [tableZero, if_pos hk, if_pos hj, if_neg hh]
    simp only [Prod.mk.injEq]
    exact ⟨by ring, trivial⟩
end FourierJacobi.Analysis
