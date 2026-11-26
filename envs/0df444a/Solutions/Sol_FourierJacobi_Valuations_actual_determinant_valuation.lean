-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_determinant_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:39.753917+00:00
-- url     : https://prove2.me/submissions/f2c08f84-cc80-4a40-a159-ccce48a10dc4

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Theorems.Thm_FourierJacobi_Valuations_nonzero_of_integer_valuation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (x y z : K) (r j h c : ℤ)
    (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (hc : 2 * h = j - r → v (y ^ 2 / (x * z) - 1) = c) :
    v (y ^ 2 - x * z) = (determinantValuation r j h c : WithTop ℤ) := by
  have hxx := nonzero_of_integer_valuation v x j hj
  have hzz := nonzero_of_integer_valuation v z (-r) hz
  have hy2 : v (y ^ 2) = ((2 * h : ℤ) : WithTop ℤ) := by
    simp [hh, two_nsmul, two_mul]
  have hxz : v (x * z) = ((j - r : ℤ) : WithTop ℤ) := by
    simp [hj, hz, sub_eq_add_neg]
  by_cases heq : 2 * h = j - r
  · have hfactor : y ^ 2 - x * z = (x * z) * (y ^ 2 / (x * z) - 1) := by
      field_simp
    rw [hfactor, v.map_mul, hc heq, hxz, ← heq]
    simp [determinantValuation, heq]
  · have hne : v (y ^ 2) ≠ v (x * z) := by
      rw [hy2, hxz]
      exact_mod_cast heq
    rw [sub_eq_add_neg, v.map_add_of_distinct_val (by simpa using hne), v.map_neg,
      hy2, hxz]
    simp [determinantValuation, heq]
end FourierJacobi.Valuations
