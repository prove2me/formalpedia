-- Prove2me | solution 1 for Comp.MatrixGameQ.value_eq_of_find
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:46:29.969575+00:00
-- url     : https://prove2.me/submissions/df530735-1186-4289-b2dd-0950c2d2b3fc

import Definitions.Def_Comp_MatrixGameQ
import Definitions.Def_Comp_Search
import Theorems.Thm_Comp_MatrixGameQ_valueCert_of_find
import Theorems.Thm_Comp_MatrixGameQ_value_eq_of_valueCert


set_option autoImplicit true
open Comp
open Csg
open Comp.MatrixGameQ
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
namespace Comp.MatrixGameQ
theorem _root_.solution {G : MatrixGameQ I J} {Is : List I} {Js : List J}
    {t : ℚ} {p : I → ℚ} {q : J → ℚ}
    (h : G.findValueCert Is Js = some (t, p, q)) : G.toMatrixGame.value = ((t : ℚ) : ℝ) :=
  value_eq_of_valueCert (valueCert_of_find h)
end Comp.MatrixGameQ
