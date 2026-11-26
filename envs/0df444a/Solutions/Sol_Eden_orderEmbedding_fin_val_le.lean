-- Prove2me | solution 1 for Eden.orderEmbedding_fin_val_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:05.993038+00:00
-- url     : https://prove2.me/submissions/8fd7509b-6b5a-4a56-86ca-e7102bfb2710

import Definitions.Def_Eden_Sorting
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Hom.PowersetCard
import Definitions.Def_Eden_SelectedSums

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {k n : ℕ} (e : Fin k ↪o Fin n) (i : Fin k) :
    i.val ≤ (e i).val := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have h : (e i.castSucc).val < (e i.succ).val := e.strictMono Fin.castSucc_lt_succ
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih h)
end Eden
