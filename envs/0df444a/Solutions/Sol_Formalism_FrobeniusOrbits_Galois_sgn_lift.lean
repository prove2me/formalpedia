-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.sgn_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:56:08.651727+00:00
-- url     : https://prove2.me/submissions/e5ba4873-d9d2-4266-a6b4-67f8f4642629

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution {σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b} {τ : Gal(L/ℚ)}
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) (x : hostE ζ a b) :
    sgn σ x = sgn τ (x : L) := by
  have key : σ x = x ↔ τ (x : L) = x := by
    rw [← hστ x]
    exact Subtype.ext_iff
  rw [sgn.eq_1, sgn.eq_1]
  by_cases hx : σ x = x
  · rw [if_pos hx, if_pos (key.1 hx)]
  · rw [if_neg hx, if_neg (fun h' => hx (key.2 h'))]
end Formalism.FrobeniusOrbits.Galois
