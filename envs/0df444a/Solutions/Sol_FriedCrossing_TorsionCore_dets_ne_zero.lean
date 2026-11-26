-- Prove2me | solution 1 for FriedCrossing.TorsionCore.dets_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:53.839052+00:00
-- url     : https://prove2.me/submissions/3e912785-c0a0-41ab-9196-4b91e3a6b249

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
theorem _root_.solution (x l : K) (hl : l ≠ 0) (hlx : l + x ≠ 0) :
    (D₂mat : Matrix (Fin 3) (Fin 3) K).det ≠ 0 ∧ (D₃mat x l).det ≠ 0 ∧ (D₄mat l).det ≠ 0 := by
  rw [det_D₂mat, det_D₃mat, det_D₄mat]
  exact ⟨by norm_num, neg_ne_zero.mpr hlx, hl⟩
end FriedCrossing.TorsionCore
