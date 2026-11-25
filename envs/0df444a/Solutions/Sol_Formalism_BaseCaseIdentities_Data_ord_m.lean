-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.ord_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:07:06.27187+00:00
-- url     : https://prove2.me/submissions/f2896050-2747-4f4e-9dae-2599c0af4e58

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_m_closed
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum


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
variable {k : Type*} [Field k] {Z C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution {s : ℕ} (hs : s < D.K) (c : C) : OrdGE 1 (D.m s c) := by
  obtain ⟨P, _, _, hP3⟩ := D.m_closed s hs
  rw [hP3 c]
  apply OrdGE.C_mul
  apply OrdGE.sum
  intro d _
  apply OrdGE.C_mul
  exact OrdGE.mono (Nat.one_le_pow _ _ D.q_pos) (OrdGE.pow (OrdGE.X d) _)
end Formalism.BaseCaseIdentities.Data
