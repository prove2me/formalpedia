-- Prove2me | solution 1 for FD1D.leafCount_le_depthTarget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:59.772572+00:00
-- url     : https://prove2.me/submissions/62e4ae49-1654-4436-978d-7e46a0175a82

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_depthTarget_ne_zero

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    leafCount m ≤ depthTarget m := by
  exact Nat.pow_log_le_self 2 (depthTarget_ne_zero m)
end FD1D
