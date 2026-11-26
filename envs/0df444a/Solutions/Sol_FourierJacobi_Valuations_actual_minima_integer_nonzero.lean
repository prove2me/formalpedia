-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_minima_integer_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:37.416784+00:00
-- url     : https://prove2.me/submissions/1074a73a-3dc0-4488-8e0b-5424ddad99e2

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Theorems.Thm_FourierJacobi_Valuations_actual_entry_minimum_integer_nonzero
import Theorems.Thm_FourierJacobi_Valuations_actual_minor_minimum_integer_nonzero
import Theorems.Thm_FourierJacobi_Valuations_nonzero_of_integer_valuation
import Theorems.Thm_FourierJacobi_Valuations_actual_determinant_valuation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (r k j h c : ℤ) (hr : r ≠ 0)
    (hk : v a = k) (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (hc : 2 * h = j - r → v (y ^ 2 / (x * z) - 1) = c) :
    matrixMinimum v (g a x y z) = (entryMinimum r k j h : WithTop ℤ) ∧
      matrixMinimum v (secondCompound (g a x y z)) =
        (minorMinimum r k j h c : WithTop ℤ) := by
  exact ⟨actual_entry_minimum_integer_nonzero v a x y z r k j h hr hk hj hh hz,
    actual_minor_minimum_integer_nonzero v a x y z r k j h c hr
      (nonzero_of_integer_valuation v a k hk) hk hj hh hz
      (actual_determinant_valuation v x y z r j h c hj hh hz hc)⟩
end FourierJacobi.Valuations
