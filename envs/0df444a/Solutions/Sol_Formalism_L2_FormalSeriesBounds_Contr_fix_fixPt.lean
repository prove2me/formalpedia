-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Contr.fix_fixPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:57:09.653142+00:00
-- url     : https://prove2.me/submissions/8b2d1c51-bf44-4e1f-93cc-8eb68a47d0cb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_noConst_iterate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_noConst_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_coeff_iterate_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_fixPt_close
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_noConst_fixPt
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_iterate_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_fixPt_close
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_fixPt
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_iterate
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {k : Type*} [Field k] {Z B : Type*}
open Formalism.L2.FormalSeriesBounds.Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H
namespace Formalism.L2.FormalSeriesBounds.Contr
theorem _root_.solution : Ψ H.fixPt = H.fixPt := by
  funext c
  ext A
  have h1 := H.contr H.fixPt (Ψ^[A.degree] 0) A.degree H.noConst_fixPt
    (H.noConst_iterate noConst_zero _) (fun c' => H.fixPt_close A.degree c') c A (by omega)
  rw [map_sub, sub_eq_zero, ← Function.iterate_succ_apply' Ψ A.degree 0] at h1
  rw [h1, H.coeff_iterate_zero c A (Nat.le_succ _)]
end Formalism.L2.FormalSeriesBounds.Contr
