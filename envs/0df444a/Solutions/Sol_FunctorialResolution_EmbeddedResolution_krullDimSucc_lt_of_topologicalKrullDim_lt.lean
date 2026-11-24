-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.krullDimSucc_lt_of_topologicalKrullDim_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:51:02.146313+00:00
-- url     : https://prove2.me/submissions/d5d89887-e966-44f0-a2e0-3a74974cc82e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_lastIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_toSequenceOfBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_withBotSuccToNat_bot
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_withBotSuccToNat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups


section
universe u v
open TopologicalSpace AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem withBotSuccToNat_lt_withBotSuccToNat {a b : WithBot ℕ∞} (h : a < b) (hb : b < ⊤) :
    withBotSuccToNat a < withBotSuccToNat b := by
  induction b using WithBot.recBotCoe with
  | bot => exact absurd h not_lt_bot
  | coe n =>
    have hn : n ≠ ⊤ := by
      rintro rfl
      exact lt_irrefl _ hb
    induction a using WithBot.recBotCoe with
    | bot =>
      rw [withBotSuccToNat_bot, withBotSuccToNat_coe]
      omega
    | coe m =>
      have hmn : m < n := WithBot.coe_lt_coe.mp h
      have hm : m ≠ ⊤ := ne_top_of_lt hmn
      obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp hm
      obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hn
      subst hM
      subst hN
      rw [withBotSuccToNat_coe, withBotSuccToNat_coe]
      have hMN : M < N := by exact_mod_cast hmn
      have e1 : ((M : ℕ∞)).toNat = M := by simp
      have e2 : ((N : ℕ∞)).toNat = N := by simp
      omega
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Z X : Scheme.{u})
    (h : topologicalKrullDim ↥Z < topologicalKrullDim ↥X)
    (hfin : topologicalKrullDim ↥X < ⊤) :
    krullDimSucc Z < krullDimSucc X := withBotSuccToNat_lt_withBotSuccToNat h hfin
end FunctorialResolution.EmbeddedResolution
