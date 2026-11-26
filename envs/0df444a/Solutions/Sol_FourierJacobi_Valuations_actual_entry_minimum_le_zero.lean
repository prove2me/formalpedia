-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_entry_minimum_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:33.268978+00:00
-- url     : https://prove2.me/submissions/5bb9adc0-0411-469c-be00-eb0e20bfdfe9

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
    (a x y z : K) : matrixMinimum v (g a x y z) ≤ 0 := by
  rw [actual_entry_minimum]
  simp [entryListMinimum]
end FourierJacobi.Valuations
