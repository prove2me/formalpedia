-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Inertia.algebraMap_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:15:45.479123+00:00
-- url     : https://prove2.me/submissions/fafec839-daae-46c9-b39d-9c23dbd7583d

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Inertia
theorem _root_.solution (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) (x : 𝓞 (hostE ζ a b)) :
    algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (σ • x) = τ • algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x := by
  apply NumberField.RingOfIntegers.ext
  show (((σ ((x : hostE ζ a b)) : hostE ζ a b)) : L) = τ (((x : hostE ζ a b)) : L)
  exact hστ _
end Formalism.FrobeniusOrbits.Inertia
