-- Prove2me | solution 1 for FD1D.treeDepth_le_clog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:07.054197+00:00
-- url     : https://prove2.me/submissions/ee82dce5-b620-455a-b219-a17c7a1d9749

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_depthTarget_le

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    treeDepth m ≤ Nat.clog 2 (m + 1) := by
  calc
    treeDepth m = Nat.log 2 (depthTarget m) := rfl
    _ ≤ Nat.log 2 m := Nat.log_mono_right (depthTarget_le hm)
    _ ≤ Nat.clog 2 m := Nat.log_le_clog 2 m
    _ ≤ Nat.clog 2 (m + 1) :=
      Nat.clog_mono_right 2 (Nat.le_succ m)
end FD1D
