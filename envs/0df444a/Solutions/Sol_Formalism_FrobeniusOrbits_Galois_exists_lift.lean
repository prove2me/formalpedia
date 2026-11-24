-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:57:13.512259+00:00
-- url     : https://prove2.me/submissions/9d281a2c-990d-4676-aa6e-556b9d8371d4

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
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    ∃ τ : Gal(L/ℚ), ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x := by
  haveI := (layer_galois hqd h).1
  exact ⟨σ.liftNormal L, fun x => (σ.liftNormal_commutes L x).symm⟩
end Formalism.FrobeniusOrbits.Galois
