-- Prove2me | solution 1 for Comp.MatrixGameQ.valueCert_of_find
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:43:55.351442+00:00
-- url     : https://prove2.me/submissions/63e12e6f-2e21-4618-acf5-bd5bbb87eada

import Definitions.Def_Comp_MatrixGameQ
import Definitions.Def_Comp_Search
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A



set_option autoImplicit true
open Comp
open Csg
open Comp.MatrixGameQ
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
namespace Comp.MatrixGameQ
theorem _root_.solution {G : MatrixGameQ I J} {Is : List I} {Js : List J}
    {t : ℚ} {p : I → ℚ} {q : J → ℚ}
    (h : G.findValueCert Is Js = some (t, p, q)) : G.ValueCert t p q := by
  unfold findValueCert at h
  have hb := List.find?_some (p := G.certOK) h
  simp only [certOK] at hb
  exact of_decide_eq_true hb
end Comp.MatrixGameQ
