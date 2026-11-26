-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_minor_minimum_integer_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:27.822738+00:00
-- url     : https://prove2.me/submissions/e785d446-2b99-48d9-a0c1-09abaac10a26

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
    (a x y z : K) (r k j h c : ℤ) (hr : r ≠ 0) (ha : a ≠ 0)
    (hk : v a = k) (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (hd : v (y ^ 2 - x * z) = (determinantValuation r j h c : WithTop ℤ)) :
    matrixMinimum v (secondCompound (g a x y z)) = (minorMinimum r k j h c : WithTop ℤ) := by
  rw [actual_minor_minimum v a x y z ha]
  unfold minorListMinimum
  rw [v.map_mul a (y ^ 2 - x * z), hd]
  simp [minorMinimum, baseMinimum, hr, hk, hj, hh, hz, sub_eq_add_neg, add_comm]
  simp only [add_min, min_assoc, add_comm]
end FourierJacobi.Valuations
