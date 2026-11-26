-- Prove2me | solution 1 for FD1D.V5.hierarchicalMemoryCount_isBigO_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:53:20.893317+00:00
-- url     : https://prove2.me/submissions/68a0ce63-7988-42f8-8982-f75b6e8dc4ea

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_Complexity
import Theorems.Thm_FD1D_V5_hierarchicalMemoryCount_le_five_mul

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution :
    (fun m : ℕ => (hierarchicalMemoryCount m : ℝ)) =O[atTop]
      (fun m : ℕ => (m : ℝ)) := by
  refine IsBigO.of_bound 5 ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hierarchicalMemoryCount_le_five_mul hm
end FD1D.V5
