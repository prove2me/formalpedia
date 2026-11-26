-- Prove2me | solution 1 for FD1D.V5.treeDepth_le_clog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:41.853801+00:00
-- url     : https://prove2.me/submissions/461ffa8f-b28a-4c39-bdb7-b80ece153857

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_depthTarget_le

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    treeDepth m ≤ Nat.clog 2 (m + 1) := by
  calc
    treeDepth m = Nat.log 2 (depthTarget m) := rfl
    _ ≤ Nat.log 2 m := Nat.log_mono_right (depthTarget_le hm)
    _ ≤ Nat.clog 2 m := Nat.log_le_clog 2 m
    _ ≤ Nat.clog 2 (m + 1) :=
      Nat.clog_mono_right 2 (Nat.le_succ m)
end FD1D.V5
