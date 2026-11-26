-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_minor_minimum_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:20.934177+00:00
-- url     : https://prove2.me/submissions/264e1010-b0b9-4ab6-95a3-e5e263b8ded9

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Theorems.Thm_FourierJacobi_Valuations_actual_minor_minimum

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (ha : a ≠ 0) :
    matrixMinimum v (secondCompound (g a x y z)) ≤ 0 := by
  rw [actual_minor_minimum v a x y z ha]
  simp [minorListMinimum]
end FourierJacobi.Valuations
