-- Prove2me | solution 1 for FD1D.one_div_leafCount_le_two_mul_parameterA_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:35.432125+00:00
-- url     : https://prove2.me/submissions/16f4ee50-be6c-4e66-8292-efdec62e1f8c

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_leafCount_cast_pos
import Theorems.Thm_FD1D_m_le_two_mul_parameterA_mul_leafCount

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ}
    (hm : 1 ≤ m) :
    (1 : ℝ) / leafCount m ≤ 2 * parameterA m / m := by
  apply (div_le_div_iff₀ (leafCount_cast_pos m)
    (by exact_mod_cast hm)).2
  norm_num
  exact_mod_cast m_le_two_mul_parameterA_mul_leafCount hm
end FD1D
