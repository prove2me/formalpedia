-- Prove2me | solution 1 for FD1D.parameterA_cast_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:39.849846+00:00
-- url     : https://prove2.me/submissions/2ca5aeb4-0ecf-47c4-b20b-4ae67053b74b

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_parameterA_cast_le_logb

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤
      (800 / Real.log 2) * Real.log m := by
  calc
    (parameterA m : ℝ) ≤ 800 * Real.logb 2 m :=
      parameterA_cast_le_logb hm
    _ = (800 / Real.log 2) * Real.log m := by
      rw [← Real.log_div_log]
      ring
end FD1D
