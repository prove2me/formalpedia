-- Prove2me | solution 1 for FD1D.V5.hierarchicalOperationCount_isBigO_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:53:15.791224+00:00
-- url     : https://prove2.me/submissions/b2f3500d-564d-4c8c-8bf2-38978f173037

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_Complexity
import Theorems.Thm_FD1D_V5_hierarchicalOperationCount_cast_le_log

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution :
    (fun m : ℕ => (hierarchicalOperationCount m : ℝ)) =O[atTop]
      (fun m : ℕ => Real.log (m : ℝ)) := by
  refine IsBigO.of_bound (100 / Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega)))]
  exact hierarchicalOperationCount_cast_le_log hm
end FD1D.V5
