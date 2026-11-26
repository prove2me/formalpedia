-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_minor_minimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:15.828988+00:00
-- url     : https://prove2.me/submissions/ae12929a-2e58-48a6-9460-df65f56a3f01

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Theorems.Thm_FourierJacobi_Valuations_le_matrixMinimum_iff
import Theorems.Thm_FourierJacobi_Valuations_matrixMinimum_le_entry
import Theorems.Thm_FourierJacobi_LocalMatrix_all_two_by_two_minors


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (ha : a ≠ 0) :
    matrixMinimum v (secondCompound (g a x y z)) = minorListMinimum v a x y z := by
  rw [all_two_by_two_minors a x y z ha]
  apply le_antisymm
  · simp only [minorListMinimum, le_min_iff]
    have h := matrixMinimum_le_entry v
      (!![a, a * x, a * y, -a * y, -a * z, a * (y ^ 2 - x * z);
         0, a⁻¹, 0, 0, 0, -z / a;
         0, 0, 1, 0, 0, y;
         0, 0, 0, 1, 0, -y;
         0, 0, 0, 0, a, a * x;
         0, 0, 0, 0, 0, a⁻¹] : Matrix (Fin 6) (Fin 6) K)
    exact ⟨⟨⟨⟨⟨⟨⟨⟨by simpa using h 2 2, by simpa using h 0 0⟩,
      by simpa using h 1 1⟩, by simpa using h 0 1⟩, by simpa using h 2 5⟩,
      by simpa using h 0 2⟩, by simpa using h 0 4⟩,
      by simpa [neg_div] using h 1 5⟩, by simpa using h 0 5⟩
  · apply (le_matrixMinimum_iff v _ _).mpr
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [minorListMinimum, neg_div]
end FourierJacobi.Valuations
