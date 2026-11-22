-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.real_subfield_real_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:16:46.445843+00:00
-- url     : https://prove2.me/submissions/90ca5e60-2fe3-422d-ae72-b903c830ab09

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_real_theta
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_real_on_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.RealCyclotomicSubfield
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.FrobeniusOrbits.RealCyclotomicSubfield
theorem _root_.solution {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    ∀ x ∈ F1 ζ, ∀ φ : L →+* ℂ, starRingEnd ℂ (φ x) = φ x := by
  intro x hx φ
  exact real_on_adjoin (ζ + ζ⁻¹) φ (real_theta (by positivity) hζ φ) x hx
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
