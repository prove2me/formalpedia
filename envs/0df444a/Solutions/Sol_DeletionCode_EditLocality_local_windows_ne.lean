-- Prove2me | solution 1 for DeletionCode.EditLocality.local_windows_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:00.181397+00:00
-- url     : https://prove2.me/submissions/7c52ef39-da06-44b6-b38e-085f3cfe1b9a

import Definitions.Def_DeletionCode_EditRigidity
import Mathlib.Order.Interval.Set.Basic
import Definitions.Def_DeletionCode_EditLocality
import Theorems.Thm_DeletionCode_EditLocality_local_output_bound
import Theorems.Thm_DeletionCode_EditLocality_origin_in_source_interval
import Theorems.Thm_DeletionCode_EditRigidity_shared_source_letters


set_option autoImplicit true
open DeletionCode DeletionCode.EditLocality
open Windows HeaderRecovery SingleEditOrigins
namespace DeletionCode.EditLocality
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e f : Edit) (he : e.Valid n) (hf : f.Valid n)
    (s p t q : ℕ) (hei : Inside e s p) (hfi : Inside f t q)
    (hsp : s + p ≤ n) (htq : t + q ≤ n)
    (hdis : Disjoint (Set.Ico s (s + p)) (Set.Ico t (t + q)))
    (a b : ℕ) (ha : s ≤ a) (hb : t ≤ b)
    (haend : a + (windowLength k - 1) ≤ s + e.outputLength p)
    (hbend : b + (windowLength k - 1) ≤ t + f.outputLength q) :
    ¬ Agree (e.word x) a (f.word x) b (windowLength k - 1) := by
  intro hag
  have heout := local_output_bound e s p n hei hsp
  have hfout := local_output_bound f t q n hfi htq
  obtain ⟨offset, r, hoffset, _, horigin⟩ :=
    EditRigidity.shared_source_letters hk x hx e f he hf a b (by omega) (by omega) hag
  have hzero := horigin 0 (by omega)
  have hre := origin_in_source_interval e s p (a + offset + 0) (r + 0) hei
    (by omega) (by omega) hzero.1
  have hrf := origin_in_source_interval f t q (b + offset + 0) (r + 0) hfi
    (by omega) (by omega) hzero.2
  exact Set.disjoint_left.mp hdis hre hrf
end DeletionCode.EditLocality
