-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:24:23.091275+00:00
-- url     : https://prove2.me/submissions/74ff18dc-db25-4fd5-b3b0-dbed3a578f6d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_withBotSuccToNat_bot
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_withBotSuccToNat_coe
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (X Y : Scheme.{u})
    (h : topologicalKrullDim ↥X ≤ topologicalKrullDim ↥Y)
    (hY : topologicalKrullDim ↥Y < ⊤) :
    krullDimSucc X ≤ krullDimSucc Y := by
  rcases eq_or_ne (topologicalKrullDim ↥X) ⊥ with hX | hX
  · simp [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, hX, withBotSuccToNat_bot]
  · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hX
    have hYne : topologicalKrullDim ↥Y ≠ ⊥ := by
      intro hb0
      rw [hb0, le_bot_iff] at h
      exact hX h
    obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hYne
    have hab : a ≤ b := by
      rw [← ha, ← hb] at h
      exact_mod_cast h
    have hbtop : b ≠ ⊤ := by
      intro hbt
      rw [← hb, hbt] at hY
      exact lt_irrefl _ hY
    have hatop : a ≠ ⊤ := by
      intro hat
      rw [hat, top_le_iff] at hab
      exact hbtop hab
    have hle : a.toNat ≤ b.toNat := by
      lift a to ℕ using hatop
      lift b to ℕ using hbtop
      simpa using hab
    rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim X, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim Y, ← ha, ← hb, withBotSuccToNat_coe, withBotSuccToNat_coe]
    omega
end FunctorialResolution.EmbeddedResolution
