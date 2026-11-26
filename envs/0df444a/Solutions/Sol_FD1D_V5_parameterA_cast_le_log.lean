-- Prove2me | solution 1 for FD1D.V5.parameterA_cast_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:08.843797+00:00
-- url     : https://prove2.me/submissions/c2aef571-2d23-49fd-9b66-c804a2c49658

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_parameterA_cast_le_logb

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤
      (8000 / Real.log 2) * Real.log (m : ℝ) := by
  calc
    (parameterA m : ℝ) ≤ 8000 * Real.logb 2 m :=
      parameterA_cast_le_logb hm
    _ = (8000 / Real.log 2) * Real.log (m : ℝ) := by
      rw [← Real.log_div_log]
      ring
end FD1D.V5
