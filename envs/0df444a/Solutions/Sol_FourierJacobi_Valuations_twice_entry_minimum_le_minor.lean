-- Prove2me | solution 1 for FourierJacobi.Valuations.twice_entry_minimum_le_minor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:07.326792+00:00
-- url     : https://prove2.me/submissions/9dc15fca-1322-46ed-b719-7b36c0f6c63e

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
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (A : Matrix (Fin 4) (Fin 4) K) :
    matrixMinimum v A + matrixMinimum v A ≤ matrixMinimum v (secondCompound A) := by
  apply (le_matrixMinimum_iff v _ _).mpr
  intro i j
  apply v.map_le_sub
  · rw [v.map_mul]
    exact add_le_add (matrixMinimum_le_entry v A _ _) (matrixMinimum_le_entry v A _ _)
  · rw [v.map_mul]
    exact add_le_add (matrixMinimum_le_entry v A _ _) (matrixMinimum_le_entry v A _ _)
end FourierJacobi.Valuations
