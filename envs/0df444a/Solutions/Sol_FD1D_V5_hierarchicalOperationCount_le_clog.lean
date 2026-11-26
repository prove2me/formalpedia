-- Prove2me | solution 1 for FD1D.V5.hierarchicalOperationCount_le_clog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:34.69685+00:00
-- url     : https://prove2.me/submissions/b19b33b7-ead2-47ab-af5e-54c760424590

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_Complexity
import Theorems.Thm_FD1D_V5_treeDepth_le_clog


set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution
    {m : ℕ} (hm : 1 ≤ m) :
    hierarchicalOperationCount m ≤
      20 * (Nat.clog 2 (m + 1) + 1) := by
  unfold hierarchicalOperationCount
  exact Nat.mul_le_mul_left 20
    (Nat.add_le_add_right (treeDepth_le_clog hm) 1)
end FD1D.V5
