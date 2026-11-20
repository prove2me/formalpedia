-- Prove2me | solution 1 for DeletionCode.SingleEditOrigins.Edit.origin_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:15.384422+00:00
-- url     : https://prove2.me/submissions/32140894-50c0-4e4b-830e-2eb5de679277

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_SingleEditOrigins

set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditOrigins
open Windows
open DeletionCode.SingleEditOrigins.Edit
namespace DeletionCode.SingleEditOrigins.Edit
theorem _root_.solution (e : Edit) {n i r : ℕ} (hv : e.Valid n)
    (hi : i < e.outputLength n) (hr : e.origin i = some r) : r < n := by
  cases e with
  | unchanged =>
    have hir := Option.some.inj hr
    change i < n at hi
    omega
  | delete pos =>
    by_cases hcut : i < pos <;>
      simp only [Valid, outputLength, origin, hcut, ite_true, ite_false,
        Option.some.injEq] at hv hi hr <;> omega
  | insert pos bit =>
    by_cases hcut : i < pos <;> by_cases heq : i = pos <;>
      simp_all only [Valid, outputLength, origin, ite_true, ite_false,
        Option.some.injEq, reduceCtorEq] <;> omega
end DeletionCode.SingleEditOrigins.Edit
