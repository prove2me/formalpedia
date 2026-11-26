-- Prove2me | solution 1 for FD1D.V5.leafCount_le_depthTarget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:09.34909+00:00
-- url     : https://prove2.me/submissions/b43c6aa9-a98b-477e-8b90-a7aa96cd06b4

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_depthTarget_pos

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution (m : ℕ) :
    leafCount m ≤ depthTarget m := by
  exact Nat.pow_log_le_self 2 (depthTarget_pos m).ne'
end FD1D.V5
