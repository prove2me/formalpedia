-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.rowShift_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:59:39.192217+00:00
-- url     : https://prove2.me/submissions/273b7cbc-5844-4503-9c72-4a40f4ce7887

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_keyL_inj
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (σ : T) (i i' : Fin (r σ)) (t : C) (ℓ : Letter T r n) :
    rowShift r n C σ i i' t (X ℓ) =
      if keyL ℓ = (σ, i.val, ℓ.2.2) then X ℓ + MvPolynomial.C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ := by
  unfold rowShift
  simp only [MvPolynomial.aeval_X]
  have key : (∃ b, ℓ = ⟨σ, (i, b)⟩) ↔ keyL ℓ = (σ, ↑i, ℓ.snd.2) := by
    constructor
    · rintro ⟨b, rfl⟩
      rfl
    · intro h
      exact ⟨ℓ.snd.2, keyL_inj (show keyL ℓ = keyL ⟨σ, (i, ℓ.snd.2)⟩ from h)⟩
  by_cases h : keyL ℓ = (σ, ↑i, ℓ.snd.2)
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (mt key.mp h), if_neg h]
end Formalism.L2.FormalSeriesBounds.RF
