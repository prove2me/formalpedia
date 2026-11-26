-- Prove2me | solution 1 for FD1D.V5.one_div_leafCount_le_two_mul_parameterA_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:28.283117+00:00
-- url     : https://prove2.me/submissions/beb5ff16-67bc-47a3-a1e6-ba83cfb63272

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_leafCount_cast_pos
import Theorems.Thm_FD1D_V5_m_le_two_mul_parameterA_mul_leafCount

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution {m : ℕ}
    (hm : 1 ≤ m) :
    (1 : ℝ) / leafCount m ≤ 2 * parameterA m / m := by
  apply (div_le_div_iff₀ (leafCount_cast_pos m)
    (by exact_mod_cast hm)).2
  norm_num
  exact_mod_cast m_le_two_mul_parameterA_mul_leafCount hm
end FD1D.V5
