-- Prove2me | solution 1 for Comp.MatrixGameQ.value_eq_of_nashCert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:23:24.07213+00:00
-- url     : https://prove2.me/submissions/f0377a3e-0459-4980-ba50-751d19c4f587

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
import Theorems.Thm_Comp_MatrixGameQ_value_eq_of_valueCert
import Theorems.Thm_Comp_MatrixGameQ_valueCert_of_nashCert

set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ
namespace Comp.MatrixGameQ
theorem _root_.solution {G : MatrixGameQ I J} {p : I → ℚ} {q : J → ℚ}
    (h : G.toBimatrixQ.NashCert p q) :
    G.toMatrixGame.value = ((G.toBimatrixQ.colPayoff p q : ℚ) : ℝ) :=
  value_eq_of_valueCert (valueCert_of_nashCert h)
end Comp.MatrixGameQ
