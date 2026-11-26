-- Prove2me | solution 1 for FourierJacobi.Valuations.cartanEliminator_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:08.950817+00:00
-- url     : https://prove2.me/submissions/ec22da00-f717-4f50-9845-9bd57fec916d

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
theorem _root_.solution (d b₁ b₂ c : K) :
    (cartanEliminator d b₁ b₂ c).transpose * J * cartanEliminator d b₁ b₂ c = J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartanEliminator, J, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ] <;> ring
end FourierJacobi.Valuations
