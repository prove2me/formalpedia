-- Prove2me | solution 1 for Comp.MatrixGameQ.toBimatrixQ_sum_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:40:58.355244+00:00
-- url     : https://prove2.me/submissions/785ab7b6-4c68-4d32-8791-ab07f0e966b1

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A

set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ
namespace Comp.MatrixGameQ
theorem _root_.solution (G : MatrixGameQ I J) (q : J → ℚ) (i : I) :
    ∑ j, G.toBimatrixQ.R i j * q j = -(∑ j, G.A i j * q j) := by
  simp [toBimatrixQ, neg_mul]
end Comp.MatrixGameQ
