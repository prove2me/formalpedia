-- Prove2me | solution 1 for Formalism.NG.cupKillAdm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:17:58.451927+00:00
-- url     : https://prove2.me/submissions/0bec1443-c348-4648-9569-d2e40e85470e

import Definitions.Def_Formalism_CharacterColumnKernels_StatGlobalModule
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NG
open Module
namespace Formalism.NG
theorem _root_.solution : StatCupKillAdm := by
  intro O D M₁ M₂ M₂' N N' M₁'' M₂'' P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₂' ρN ρN' ρ₁'' ρ₂'' ρP
    β β' γ j ι π φ ψ CN2 CN CN' CP hβ hβ' hj hι hπ hφ hψ hcomp hγ hCP hH2 a b e ha hb he hc2 hc1
  have hz : cup1 ρ₂ β a b ∈ characterColumnKernelPairSetVariant ρN := by
    intro g h k
    simp only [cup1]
    rw [← hβ g (a h) (ρ₂ h (b k)), ha g h, hb h k, map_mul, Module.End.mul_apply]
    simp only [map_add, LinearMap.add_apply]
    abel
  obtain ⟨c, hcN, hc⟩ := hH2 _ hz hc2 ⟨_, hc1, by
    intro g h
    simp only [cup1, hcomp, map_neg]
    rw [hj g (b h), he h, ← hβ' g (a h) (ρ₂' h e), ha g h, map_mul, Module.End.mul_apply]
    simp only [map_sub, map_add, LinearMap.add_apply]
    abel⟩
  refine ⟨fun g => ψ (c g), hCP _ hcN, ?_⟩
  intro g h
  simp only [cup1]
  rw [← hφ g (b h), hγ, ← hψ g, ← map_sub, ← map_add]
  exact congrArg ψ (hc g h)
end Formalism.NG
