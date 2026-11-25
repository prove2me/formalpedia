-- Prove2me | solution 1 for Formalism.NG.congBoundLarge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:17:54.073405+00:00
-- url     : https://prove2.me/submissions/f9793143-808f-4fbf-b520-4189946dfd1d

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_mem_Vx
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_cc_comm
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_cc_mem_VS
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_vcc_attain
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_congMod_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open QuotientPowerLengths
namespace Formalism.NG
theorem _root_.solution : StatCongBoundLarge := by
  unfold StatCongBoundLarge
  intro O _ _ _ X _ T _ _ V _ _ _ _ _ act hsum L hL _ hLT Z _
  refine congMod_le hsum L hL Z ((fun c : T => act c) '' (ccIdeal T (Z : Set X) : Set T))
    (vcc T (Z : Set X)) ?_ ?_ ?_ ?_
  · rintro g ⟨c, -, rfl⟩ f
    exact cc_comm c f
  · rintro g ⟨c, -, rfl⟩ v hv
    exact hLT c v hv
  · rintro g ⟨c, hc, rfl⟩ v -
    exact cc_mem_VS hsum hc v
  · intro x _
    obtain ⟨c, hc, hcx⟩ := vcc_attain (T := T) (Z : Set X) x
    exact ⟨act c, ⟨c, hc, rfl⟩, (c : X → O) x, fun v hv => (mem_Vx.mp hv) c, hcx.le⟩
end Formalism.NG
