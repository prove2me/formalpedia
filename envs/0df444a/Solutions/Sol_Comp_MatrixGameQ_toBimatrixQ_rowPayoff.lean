-- Prove2me | solution 1 for Comp.MatrixGameQ.toBimatrixQ_rowPayoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:41:29.047801+00:00
-- url     : https://prove2.me/submissions/334f8e9d-be08-4872-bf6c-9c6cd2568fa9

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
theorem _root_.solution (G : MatrixGameQ I J) (p : I → ℚ) (q : J → ℚ) :
    G.toBimatrixQ.rowPayoff p q = -(G.toBimatrixQ.colPayoff p q) := by
  simp [BimatrixQ.rowPayoff, BimatrixQ.colPayoff, toBimatrixQ, neg_mul, mul_neg]
end Comp.MatrixGameQ
