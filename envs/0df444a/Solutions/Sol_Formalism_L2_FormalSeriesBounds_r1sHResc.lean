-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.r1sHResc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:11:57.72642+00:00
-- url     : https://prove2.me/submissions/b59af990-9588-49e4-ba5b-318c67fb4ece

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RescaleInV
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjPoints_rescale_HH
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open SelfConjPoints
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (c : C) :
    HH X (rc c x) z = rs 0 c (HH X x z) ∧ HH X x (rc c z) = rs 1 c (HH X x z) := by
  have e1 : ∀ y : κ → PowerSeries C, rc 1 y = y := fun y => by
    funext i; unfold rc; rw [PowerSeries.rescale_one]; rfl
  refine ⟨?_, ?_⟩
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]
end Formalism.L2.FormalSeriesBounds
