-- Prove2me | solution 1 for FD1D.pow_le_leafCount_of_pow_le_depthTarget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:01.870935+00:00
-- url     : https://prove2.me/submissions/b55d5767-56e3-40e2-a3e8-d5b95450cc41

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_pow_le_depthTarget_iff

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m k : ℕ}
    (hk : 2 ^ k ≤ depthTarget m) :
    2 ^ k ≤ leafCount m := by
  exact Nat.pow_le_pow_right (by norm_num)
    (pow_le_depthTarget_iff.mp hk)
end FD1D
