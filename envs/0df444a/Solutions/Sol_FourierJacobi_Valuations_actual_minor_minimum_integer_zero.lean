-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_minor_minimum_integer_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:24.551858+00:00
-- url     : https://prove2.me/submissions/73c36099-89a8-47a5-8a8a-94f9c9f91ade

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
    (a x y : K) (k j h c : ℤ) (hk : v a = k) (hj : v x = j) (hh : v y = h)
    (ha : a ≠ 0) :
    matrixMinimum v (secondCompound (g a x y 0)) = (minorMinimum 0 k j h c : WithTop ℤ) := by
  rw [actual_minor_minimum v a x y 0 ha]
  simp [minorListMinimum, minorMinimum, baseMinimum, hk, hj, hh, two_nsmul, two_mul]
  simp only [add_min, min_assoc]
end FourierJacobi.Valuations
