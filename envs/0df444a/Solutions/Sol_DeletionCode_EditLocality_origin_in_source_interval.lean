-- Prove2me | solution 1 for DeletionCode.EditLocality.origin_in_source_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:28.080676+00:00
-- url     : https://prove2.me/submissions/0cfe2ab6-07ee-4859-9fb3-a7018ca4312e

import Definitions.Def_DeletionCode_EditRigidity
import Mathlib.Order.Interval.Set.Basic
import Definitions.Def_DeletionCode_EditLocality

set_option autoImplicit true
open DeletionCode DeletionCode.EditLocality
open Windows HeaderRecovery SingleEditOrigins
namespace DeletionCode.EditLocality
theorem _root_.solution (e : Edit) (start len i r : ℕ)
    (he : Inside e start len) (hstart : start ≤ i)
    (hend : i < start + e.outputLength len) (hr : e.origin i = some r) :
    start ≤ r ∧ r < start + len := by
  cases e with
  | unchanged =>
    have hir := Option.some.inj hr
    change i < start + len at hend
    omega
  | delete pos =>
    by_cases hcut : i < pos <;>
      simp only [Inside, Edit.outputLength, Edit.origin, hcut, ite_true, ite_false,
        Option.some.injEq] at he hend hr <;> omega
  | insert pos bit =>
    change start ≤ pos ∧ pos ≤ start + len at he
    change i < start + (len + 1) at hend
    by_cases hcut : i < pos
    · have hir : i = r := by
        simpa only [Edit.origin, if_pos hcut, Option.some.injEq] using hr
      omega
    · by_cases heq : i = pos
      · simp only [Edit.origin, if_neg hcut, if_pos heq, reduceCtorEq] at hr
      · have hir : i - 1 = r := by
          simpa only [Edit.origin, if_neg hcut, if_neg heq,
            Option.some.injEq] using hr
        omega
end DeletionCode.EditLocality
