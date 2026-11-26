-- Prove2me | solution 1 for FD1D.inv_horizon_le_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:30.492085+00:00
-- url     : https://prove2.me/submissions/c772a65a-7414-432b-afe7-722d8b78f3de

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Arithmetic

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    {T m : ℝ} (hm : 0 < m) (hT : m ^ 2 ≤ T) :
    1 / T ≤ 1 / m ^ 2 := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hT0 : 0 < T := lt_of_lt_of_le hm2 hT
  exact one_div_le_one_div_of_le hm2 hT
end FD1D
