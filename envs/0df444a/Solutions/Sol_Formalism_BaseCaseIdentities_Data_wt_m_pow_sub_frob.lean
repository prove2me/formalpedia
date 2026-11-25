-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.wt_m_pow_sub_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:34:38.262894+00:00
-- url     : https://prove2.me/submissions/c877afd2-d79d-4140-ba8c-da773f4ca5da

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_pow_sub_frob
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_cast
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_m_rho
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_m_closed
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
theorem _root_.solution {s : ℕ} (hs : s < D.K) (c : C) :
    D.Wt (1 + qnum D.l * rho D.l) (D.m s c ^ D.q - frob D.q (D.m s c)) := by
  obtain ⟨P, _, _, hP3⟩ := D.m_closed s hs
  have hw := D.wt_m_rho s c
  obtain ⟨κ, hκ⟩ : ∃ κ : k, κ = (-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹ := ⟨_, rfl⟩
  rw [← hκ] at hP3
  have h1 : D.m s c = ∑ d, MvPowerSeries.C (κ * P c d) * X d ^ (D.q ^ s) := by
    rw [hP3 c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul, mul_assoc]
  rw [h1] at hw ⊢
  have := hasWt_pow_sub_frob D.l_prime D.v_l (le_refl 2 |>.trans' (by norm_num : 1 ≤ 2))
    (Nat.one_le_pow _ _ D.q_pos) _ hw
  rw [← D.q_cast]
  exact this
end Formalism.BaseCaseIdentities.Data
