-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.log_nSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:22.312136+00:00
-- url     : https://prove2.me/submissions/0a5f7fd2-a891-4ac7-85d6-da1c89dd7cc9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_zero
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_succ
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_FF
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.ZSer
local notation "FF[" W "](" a ", " b ")" =>
  MvPowerSeries.subst (![a, b] : Fin 2 → PowerSeries _) (fgl W)
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.ZSer
theorem _root_.solution (hL : FglLog.{u}) (n : ℕ) :
    (logSer W).subst (nSer W n) = C (n : K) * logSer W := by
  have hX : (logSer W).subst (X : K⟦X⟧) = logSer W := by
    rw [← PowerSeries.map_algebraMap_eq_subst_X]
    rfl
  induction n with
  | zero =>
    rw [nSer_zero, Nat.cast_zero, map_zero, zero_mul]
    exact PowerSeries.subst_zero_of_constantCoeff_zero (log_cc W)
  | succ n ih =>
    rw [nSer_succ, log_FF W hL constantCoeff_X (nSer_cc W n), ih, hX, Nat.cast_succ, map_add, map_one,
      add_mul, one_mul, add_comm]
end Formalism.L2.Th1.A.ZSer
