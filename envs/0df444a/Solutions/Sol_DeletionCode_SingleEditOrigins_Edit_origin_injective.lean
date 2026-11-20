-- Prove2me | solution 1 for DeletionCode.SingleEditOrigins.Edit.origin_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:14.999502+00:00
-- url     : https://prove2.me/submissions/1905ff12-b027-4063-9cf2-decd2fb8eb6f

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_SingleEditOrigins

set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditOrigins
open Windows
open DeletionCode.SingleEditOrigins.Edit
namespace DeletionCode.SingleEditOrigins.Edit
theorem _root_.solution (e : Edit) {i j r : ℕ}
    (hi : e.origin i = some r) (hj : e.origin j = some r) : i = j := by
  cases e with
  | unchanged => exact (Option.some.inj hi).trans (Option.some.inj hj).symm
  | delete pos =>
    by_cases hiCut : i < pos <;> by_cases hjCut : j < pos <;>
      simp only [origin, hiCut, hjCut, ite_true, ite_false, Option.some.injEq] at hi hj <;>
      omega
  | insert pos bit =>
    by_cases hiCut : i < pos <;> by_cases hjCut : j < pos <;>
      by_cases hiEq : i = pos <;> by_cases hjEq : j = pos <;>
      simp_all only [origin, ite_true, ite_false, Option.some.injEq, reduceCtorEq] <;> omega
end DeletionCode.SingleEditOrigins.Edit
