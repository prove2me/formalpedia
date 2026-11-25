-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.chainII_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:37.404185+00:00
-- url     : https://prove2.me/submissions/820bceaf-8ff8-47f5-ba67-165ec936a721

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_inWTo_iff
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_start_in_W_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_psi_in_W_holds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_hasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero


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
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution : D.ChainII := by
  intro t hnc hfix
  have hit : ∀ n, NoConst ((D.Psi)^[n] D.start) ∧ D.InW ((D.Psi)^[n] D.start) := by
    intro n
    induction n with
    | zero => exact D.start_in_W_holds
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact D.psi_in_W_holds _ ih.1 ih.2
  unfold InW
  rw [inWTo_iff]
  intro c A
  have h := (D.inWTo_iff _ _).1 (hit A.degree).2 c A
  have hc := D.hasUniqueFixedPoint.2 D.start t D.start_in_W_holds.1 hnc hfix A.degree A le_rfl c
  rw [map_sub] at h ⊢
  rw [← hc]
  exact h
end Formalism.BaseCaseIdentities.Data
