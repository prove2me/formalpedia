-- Prove2me | solution 1 for Comp.MatrixGameQ.toMatrixGame_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:55.776951+00:00
-- url     : https://prove2.me/submissions/3637c362-deb2-4a3a-8c42-ae1376042570

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ

set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ
namespace Comp.MatrixGameQ
theorem _root_.solution (G : MatrixGameQ I J) (i : I) (j : J) :
    G.toMatrixGame.A i j = ((G.A i j : ℚ) : ℝ) := rfl
end Comp.MatrixGameQ
