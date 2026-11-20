-- Prove2me | solution 1 for DeletionCode.EditLocality.local_vertex_sets_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:05.91507+00:00
-- url     : https://prove2.me/submissions/18af0ba3-b8ce-4bd9-a4f2-3f7768ce7dfb

import Definitions.Def_DeletionCode_EditRigidity
import Mathlib.Order.Interval.Set.Basic
import Definitions.Def_DeletionCode_EditLocality
import Theorems.Thm_DeletionCode_EditLocality_local_windows_ne

set_option autoImplicit true
open DeletionCode DeletionCode.EditLocality
open Windows HeaderRecovery SingleEditOrigins
namespace DeletionCode.EditLocality
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e f : Edit) (he : e.Valid n) (hf : f.Valid n)
    (s p t q : ℕ) (hei : Inside e s p) (hfi : Inside f t q)
    (hsp : s + p ≤ n) (htq : t + q ≤ n)
    (hdis : Disjoint (Set.Ico s (s + p)) (Set.Ico t (t + q))) :
    Disjoint (localVertices e x s p (windowLength k))
      (localVertices f x t q (windowLength k)) := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  obtain ⟨a, ha, haend, hva⟩ := hv
  obtain ⟨b, hb, hbend, hvb⟩ := hw
  apply local_windows_ne hk x hx e f he hf s p t q hei hfi hsp htq hdis a b ha hb haend hbend
  intro i hi
  exact congrFun (hva.trans hvb.symm) ⟨i, hi⟩
end DeletionCode.EditLocality
