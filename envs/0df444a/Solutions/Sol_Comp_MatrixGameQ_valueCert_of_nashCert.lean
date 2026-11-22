-- Prove2me | solution 1 for Comp.MatrixGameQ.valueCert_of_nashCert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:45:32.232917+00:00
-- url     : https://prove2.me/submissions/7b4e1e96-9523-401d-8451-bc8983d55d9a

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ
import Theorems.Thm_Comp_MatrixGameQ_toBimatrixQ_sum_row
import Theorems.Thm_Comp_MatrixGameQ_toBimatrixQ_rowPayoff
import Theorems.Thm_Comp_MatrixGameQ_toBimatrixQ_sum_col

set_option autoImplicit true
open Comp
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Comp.MatrixGameQ
namespace Comp.MatrixGameQ
theorem _root_.solution {G : MatrixGameQ I J} {p : I → ℚ} {q : J → ℚ}
    (h : G.toBimatrixQ.NashCert p q) :
    G.ValueCert (G.toBimatrixQ.colPayoff p q) p q := by
  obtain ⟨hp, hq, hrow, hcol, -, -⟩ := h
  refine ⟨hp, hq, fun j => ?_, fun i => ?_⟩
  · have := hcol j
    rwa [toBimatrixQ_sum_col] at this
  · have hr := hrow i
    rw [toBimatrixQ_sum_row, toBimatrixQ_rowPayoff] at hr
    linarith
end Comp.MatrixGameQ
