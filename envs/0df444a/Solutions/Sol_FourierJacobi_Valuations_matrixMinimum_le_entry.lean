-- Prove2me | solution 1 for FourierJacobi.Valuations.matrixMinimum_le_entry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:36.785101+00:00
-- url     : https://prove2.me/submissions/f3a373a8-aaa0-416c-be7c-5e4a2ef4ce0f

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
import Theorems.Thm_FourierJacobi_Valuations_le_matrixMinimum_iff

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution {n m : ℕ} (v : AddValuation K (WithTop ℤ))
    (A : Matrix (Fin n) (Fin m) K) (i : Fin n) (j : Fin m) :
    matrixMinimum v A ≤ v (A i j) :=
  (le_matrixMinimum_iff v A _).mp le_rfl i j
end FourierJacobi.Valuations
