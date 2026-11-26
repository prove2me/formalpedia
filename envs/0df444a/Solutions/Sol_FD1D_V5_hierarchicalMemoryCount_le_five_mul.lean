-- Prove2me | solution 1 for FD1D.V5.hierarchicalMemoryCount_le_five_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:27.742905+00:00
-- url     : https://prove2.me/submissions/d22c35b0-a8ec-4e3a-9ba2-1357c5ce5856

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_Complexity
import Theorems.Thm_FD1D_V5_depthTarget_le
import Theorems.Thm_FD1D_V5_leafCount_le_depthTarget


set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution
    {m : ℕ} (hm : 1 ≤ m) :
    hierarchicalMemoryCount m ≤ 5 * m := by
  have hleaf : leafCount m ≤ m :=
    (leafCount_le_depthTarget m).trans (depthTarget_le hm)
  unfold hierarchicalMemoryCount
  omega
end FD1D.V5
