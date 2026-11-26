-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_entry_minimum_integer_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:37.42652+00:00
-- url     : https://prove2.me/submissions/6971bb39-47e8-4fed-811e-801266c8cc92

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Theorems.Thm_FourierJacobi_Valuations_actual_entry_minimum

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (r k j h : ℤ) (hr : r ≠ 0)
    (hk : v a = k) (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ)) :
    matrixMinimum v (g a x y z) = (entryMinimum r k j h : WithTop ℤ) := by
  rw [actual_entry_minimum]
  simp [entryListMinimum, entryMinimum, baseMinimum, hr, hk, hj, hh, hz, min_assoc]
end FourierJacobi.Valuations
