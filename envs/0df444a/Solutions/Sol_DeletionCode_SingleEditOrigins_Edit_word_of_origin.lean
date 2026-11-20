-- Prove2me | solution 1 for DeletionCode.SingleEditOrigins.Edit.word_of_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:14.616722+00:00
-- url     : https://prove2.me/submissions/b209bd8e-887f-459a-9781-26e2764a817d

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_SingleEditOrigins

set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditOrigins
open Windows
open DeletionCode.SingleEditOrigins.Edit
namespace DeletionCode.SingleEditOrigins.Edit
theorem _root_.solution (e : Edit) (x : Letters) {i r : ℕ}
    (h : e.origin i = some r) : e.word x i = x r := by
  cases e with
  | unchanged => exact congrArg x (Option.some.inj h)
  | delete pos =>
    by_cases hi : i < pos
    · have hir : i = r := by simpa only [origin, if_pos hi, Option.some.injEq] using h
      change (if i < pos then x i else x (i + 1)) = x r
      rw [if_pos hi, hir]
    · have hir : i + 1 = r := by simpa only [origin, if_neg hi, Option.some.injEq] using h
      simp only [word, deleteAt, if_neg hi, hir]
  | insert pos bit =>
    by_cases hi : i < pos
    · have hir : i = r := by simpa only [origin, if_pos hi, Option.some.injEq] using h
      change (if i < pos then x i else if i = pos then bit else x (i - 1)) = x r
      rw [if_pos hi, hir]
    · by_cases heq : i = pos
      · simp only [origin, if_neg hi, if_pos heq, reduceCtorEq] at h
      · have hir : i - 1 = r := by
          simpa only [origin, if_neg hi, if_neg heq, Option.some.injEq] using h
        simp only [word, insertAt, if_neg hi, if_neg heq, hir]
end DeletionCode.SingleEditOrigins.Edit
