-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.log_zSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:19:56.827584+00:00
-- url     : https://prove2.me/submissions/58d9eeb1-5a8d-4fff-af9e-fa7a4beaa198

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_iSer_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_zSer_negSucc
import Theorems.Thm_P2M_Formalism_L2_Th1_A_ZSer_iSerSpec__ff57dfa23ee4
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_nSer
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_composition_inverse_spec
import Theorems.Thm_Formalism_L2_Th1_A_integration_spec
import Theorems.Thm_Formalism_L2_Th1_A_invariant_differential_units
import Theorems.Thm_Formalism_L2_Th1_A_logNeg_of
import Theorems.Thm_P2M_Formalism_L2_Th1_A_subst_neg__662fad9e4892


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
theorem _root_.solution (hL : FglLog.{u}) (n : ℤ) :
    (logSer W).subst (zSer W n) = C (n : K) * logSer W := by
  rcases n with n | n
  · show (logSer W).subst (nSer W n) = C (((n : ℕ) : ℤ) : K) * logSer W
    exact_mod_cast log_nSer W hL n
  · have hs := nSer_cc W (n + 1)
    have hS : (logSer W).subst (iSer W) = -logSer W :=
      ((logNeg_of integration_spec composition_inverse_spec invariant_differential_units iSerSpec') K W).1
    rw [zSer_negSucc, ← PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (iSer_cc W))
      (HasSubst.of_constantCoeff_zero' hs), hS, subst_neg' (HasSubst.of_constantCoeff_zero' hs),
      log_nSer W hL (n + 1), Int.cast_negSucc, map_neg, neg_mul]
end Formalism.L2.Th1.A.ZSer
