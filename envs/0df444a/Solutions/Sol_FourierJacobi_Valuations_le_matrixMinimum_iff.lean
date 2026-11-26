-- Prove2me | solution 1 for FourierJacobi.Valuations.le_matrixMinimum_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:10.997748+00:00
-- url     : https://prove2.me/submissions/62a5f9d4-0b71-404c-962c-e6f102066305

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
theorem _root_.solution {n m : ℕ} (v : AddValuation K (WithTop ℤ))
    (A : Matrix (Fin n) (Fin m) K) (b : WithTop ℤ) :
    b ≤ matrixMinimum v A ↔ ∀ i j, b ≤ v (A i j) := by
  simp [matrixMinimum]
end FourierJacobi.Valuations
