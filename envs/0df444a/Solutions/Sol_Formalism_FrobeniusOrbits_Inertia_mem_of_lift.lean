-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Inertia.mem_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:43.710701+00:00
-- url     : https://prove2.me/submissions/3ad87aa4-7e7f-47f3-a4be-50fb5b49892c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_algebraMap_smul

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
theorem _root_.solution (P : Ideal (𝓞 (hostE ζ a b))) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x)
    (hσ : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) (y : 𝓞 (hostE ζ a b)) :
    τ • algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) y - algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) y ∈ Q := by
  rw [← algebraMap_smul σ τ hστ y, ← map_sub]
  have h := hσ y
  rw [Ideal.over_def Q P] at h
  exact h
end Formalism.FrobeniusOrbits.Inertia
