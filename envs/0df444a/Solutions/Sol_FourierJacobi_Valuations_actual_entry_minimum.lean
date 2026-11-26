-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_entry_minimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:13.535853+00:00
-- url     : https://prove2.me/submissions/899ff8f8-589f-4f70-b5b9-a661893407f9

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Theorems.Thm_FourierJacobi_Valuations_le_matrixMinimum_iff
import Theorems.Thm_FourierJacobi_Valuations_matrixMinimum_le_entry

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ)) (a x y z : K) :
    matrixMinimum v (g a x y z) = entryListMinimum v a x y z := by
  apply le_antisymm
  · simp only [entryListMinimum, le_min_iff]
    have h := matrixMinimum_le_entry v (g a x y z)
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 0 0)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 1 1)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 2 2)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 1 2)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 0 2)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 1 3)
    · simpa [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ] using (h 0 3)
  · apply (le_matrixMinimum_iff v _ _).mpr
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [g, D, N, Matrix.mul_apply, Fin.sum_univ_succ, entryListMinimum]
end FourierJacobi.Valuations
