-- Prove2me | solution 1 for FD1D.parameterA_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:00:02.945098+00:00
-- url     : https://prove2.me/submissions/ce0f0243-1c23-48df-a3e2-22b2999e52f0

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    0 < parameterA m := by
  unfold parameterA
  exact Nat.mul_pos (by norm_num)
    (Nat.clog_pos (by norm_num) (by omega))
end FD1D
