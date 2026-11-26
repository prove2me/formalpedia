-- Prove2me | solution 1 for FD1D.pow_le_depthTarget_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:02.851681+00:00
-- url     : https://prove2.me/submissions/e7c1bff1-2750-4b9e-92b7-5b678a17aa7e

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_depthTarget_ne_zero

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m k : ℕ} :
    2 ^ k ≤ depthTarget m ↔ k ≤ treeDepth m := by
  rw [treeDepth, Nat.le_log_iff_pow_le (by norm_num) (depthTarget_ne_zero m)]
end FD1D
