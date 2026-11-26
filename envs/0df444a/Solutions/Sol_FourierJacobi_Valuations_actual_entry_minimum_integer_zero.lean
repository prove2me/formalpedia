-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_entry_minimum_integer_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:33.966326+00:00
-- url     : https://prove2.me/submissions/aa2b1204-2f1f-4093-aaef-18885aea85df

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
    (a x y : K) (k j h : ℤ) (hk : v a = k) (hj : v x = j) (hh : v y = h) :
    matrixMinimum v (g a x y 0) = (entryMinimum 0 k j h : WithTop ℤ) := by
  rw [actual_entry_minimum]
  simp [entryListMinimum, entryMinimum, baseMinimum, hk, hj, hh, min_assoc]
end FourierJacobi.Valuations
