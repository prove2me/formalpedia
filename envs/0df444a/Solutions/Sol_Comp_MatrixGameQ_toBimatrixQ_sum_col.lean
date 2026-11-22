-- Prove2me | solution 1 for Comp.MatrixGameQ.toBimatrixQ_sum_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:42:11.343137+00:00
-- url     : https://prove2.me/submissions/419727ea-42c0-442b-8925-eb0c624013d7

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ

set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ
namespace Comp.MatrixGameQ
theorem _root_.solution (G : MatrixGameQ I J) (p : I → ℚ) (j : J) :
    ∑ i, p i * G.toBimatrixQ.C i j = ∑ i, p i * G.A i j := rfl
end Comp.MatrixGameQ
