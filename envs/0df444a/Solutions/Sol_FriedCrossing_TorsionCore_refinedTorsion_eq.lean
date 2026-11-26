-- Prove2me | solution 1 for FriedCrossing.TorsionCore.refinedTorsion_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:45:14.075128+00:00
-- url     : https://prove2.me/submissions/57398cce-3f71-42b0-88aa-28f81f1bac5b

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
import Theorems.Thm_P2M_FriedCrossing_TorsionCore_det_D_mat_fc25e0bffca9
import Theorems.Thm_P2M_FriedCrossing_TorsionCore_det_D_mat_4a6a93f491c6
import Theorems.Thm_P2M_FriedCrossing_TorsionCore_det_D_mat_da92292f3a50

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]
namespace FriedCrossing.TorsionCore
theorem _root_.solution (x l : K) (hl : l ≠ 0) : refinedTorsion x l = -(l + x) / l := by
  rw [refinedTorsion, det_D₂mat, det_D₃mat, det_D₄mat, det_fin_one]
  simp only [N_C, m_C, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  field_simp
  ring
end FriedCrossing.TorsionCore
