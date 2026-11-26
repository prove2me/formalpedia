-- Prove2me | solution 1 for FourierJacobi.Valuations.nonzero_of_integer_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:06.712671+00:00
-- url     : https://prove2.me/submissions/803b844c-0a5a-4429-b18b-00cb2d33ee77

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (x : K) (k : ℤ) (hk : v x = k) : x ≠ 0 := by
  intro hx
  simp [hx] at hk
end FourierJacobi.Valuations
