-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.Psi_fixPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:42.398313+00:00
-- url     : https://prove2.me/submissions/7267a291-25f2-440e-950c-2c8723f47f8d

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_one_lt_l
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_contracts
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_iterate
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_iterate_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_fixPt_close
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_fixPt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution : D.Psi D.fixPt = D.fixPt := by
  funext b
  ext A
  have h := D.contracts D.fixPt ((D.Psi)^[A.degree] 0) A.degree D.noConst_fixPt
    (D.noConst_iterate noConst_zero _) (fun c => D.fixPt_close A.degree c) b A
    (by have := D.one_lt_l; omega)
  rw [map_sub, sub_eq_zero, ← Function.iterate_succ_apply' D.Psi] at h
  rw [h, D.coeff_iterate_zero b A (Nat.le_succ _)]
end Formalism.BaseCaseIdentities.Data
