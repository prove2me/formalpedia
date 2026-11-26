-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_minima_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:57.721812+00:00
-- url     : https://prove2.me/submissions/89a5bc68-56d2-4def-a122-59ce1ae10836

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Theorems.Thm_FourierJacobi_Valuations_actual_entry_minimum_le_zero
import Theorems.Thm_FourierJacobi_Valuations_actual_minor_minimum_le_zero

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (ha : a ≠ 0) :
    matrixMinimum v (g a x y z) ≠ ⊤ ∧
      matrixMinimum v (secondCompound (g a x y z)) ≠ ⊤ := by
  constructor
  · exact ne_top_of_le_ne_top (by simp) (actual_entry_minimum_le_zero v a x y z)
  · exact ne_top_of_le_ne_top (by simp) (actual_minor_minimum_le_zero v a x y z ha)
end FourierJacobi.Valuations
