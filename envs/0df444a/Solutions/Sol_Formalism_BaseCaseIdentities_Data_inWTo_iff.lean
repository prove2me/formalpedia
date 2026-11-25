-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.inWTo_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:46:24.469878+00:00
-- url     : https://prove2.me/submissions/de194ebc-f828-4ec9-a9e1-b515d7ff0d3a

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds

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
theorem _root_.solution (J : ℕ) (t : C → MvPowerSeries Z k) :
    D.InWTo J t ↔ ∀ c, D.Wt D.top (t c - D.mu J c) := by
  constructor
  · intro h c
    unfold mu
    split_ifs with hc
    · exact h.1 c hc
    · rw [sub_zero]; exact h.2 c (not_lt.1 hc)
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := h c
      rwa [mu, if_pos hc] at this
    · have := h c
      rwa [mu, if_neg (not_lt.2 hc), sub_zero] at this
end Formalism.BaseCaseIdentities.Data
