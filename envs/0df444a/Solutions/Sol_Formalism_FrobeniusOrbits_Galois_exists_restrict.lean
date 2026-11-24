-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.exists_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:04:53.155381+00:00
-- url     : https://prove2.me/submissions/a343c62d-0d83-41d2-ae56-cd91a09dda39

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_isGalois_hostE

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
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (τ : Gal(L/ℚ)) :
    ∃ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x := by
  haveI := (layer_galois hqd h).1
  haveI := isGalois_hostE hqd h
  exact ⟨τ.restrictNormal (hostE ζ a b), fun x => τ.restrictNormal_commutes (hostE ζ a b) x⟩
end Formalism.FrobeniusOrbits.Galois
