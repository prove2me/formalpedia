-- Prove2me | solution 1 for FD1D.InventoryState.move_apply_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:47.672785+00:00
-- url     : https://prove2.me/submissions/eb7dce6a-d0bd-403c-bd17-ae34ce40e9aa

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.InventoryState
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace FD1D.InventoryState
theorem _root_.solution {m : ℕ} (x : InventoryState ι m) {d a i : ι}
    (hd : 0 < x.1 d) :
    (move x d a).1 i =
      x.1 i + (if i = a then 1 else 0) - (if i = d then 1 else 0) := by
  rw [move, dif_pos hd]
  by_cases hia : i = a
  · subst i
    by_cases had : a = d
    · subst d
      simp [Function.update_apply]
      omega
    · have hda : d ≠ a := Ne.symm had
      simp [Function.update_apply, had, hda]
  · by_cases hid : i = d
    · subst i
      have hda : d ≠ a := hia
      simp [Function.update_apply, hia, hda]
    · simp [Function.update_apply, hia, hid]
end FD1D.InventoryState
