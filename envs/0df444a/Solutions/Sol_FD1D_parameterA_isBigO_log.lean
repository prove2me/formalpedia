-- Prove2me | solution 1 for FD1D.parameterA_isBigO_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:35.991968+00:00
-- url     : https://prove2.me/submissions/6d598000-1080-4dc1-a96a-9406a4424051

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_parameterA_cast_le_log

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution :
    (fun m : ℕ => (parameterA m : ℝ)) =O[atTop]
      (fun m : ℕ => Real.log (m : ℝ)) := by
  refine IsBigO.of_bound (800 / Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega)))]
  exact parameterA_cast_le_log hm
end FD1D
