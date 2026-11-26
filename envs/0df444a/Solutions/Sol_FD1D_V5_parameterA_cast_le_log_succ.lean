-- Prove2me | solution 1 for FD1D.V5.parameterA_cast_le_log_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:54.045222+00:00
-- url     : https://prove2.me/submissions/049f9518-fbaa-4baf-8ca3-b8a2a89ac983

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_parameterA_cast_le_log

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤
      (8000 / Real.log 2) * Real.log ((m + 1 : ℕ) : ℝ) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmono :
      Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 1 ≤ m by omega)
    · exact_mod_cast Nat.le_succ m
  exact (parameterA_cast_le_log hm).trans
    (mul_le_mul_of_nonneg_left hmono
      (div_nonneg (by norm_num) hlogTwo.le))
end FD1D.V5
