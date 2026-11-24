-- Prove2me | solution 1 for Formalism.L2.Th1.B.SAdd.shear_two_variables_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:19.214301+00:00
-- url     : https://prove2.me/submissions/6f433318-4b88-4cad-ae95-42b8c044dfee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_eq_zero_of_shear
import Theorems.Thm_Formalism_L2_Th1_B_Add1_pd_sub
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_at_sum
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_sub
import Theorems.Thm_Formalism_L2_Th1_B_pd_atS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Formalism.L2.Th1.B.SAdd
theorem _root_.solution : ShearTwo := by
  intro K _ _ h hh
  have hk : pd 0 (h - atS (ev0 h)) = pd 1 (h - atS (ev0 h)) := by
    rw [Add1.pd_sub, Add1.pd_sub, pd_atS, pd_atS, hh]
  have h0 : ev0 (h - atS (ev0 h)) = 0 := by
    rw [eval_second_zero_sub, eval_second_zero_at_sum, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_shear hk h0)
end Formalism.L2.Th1.B.SAdd
