-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.mem_fixedField_zpowers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:56:05.596688+00:00
-- url     : https://prove2.me/submissions/aab5d750-1125-4d36-9db0-436f2e9af269

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
theorem _root_.solution (τ : Gal(L/ℚ)) (x : L) :
    x ∈ fixedField (Subgroup.zpowers τ) ↔ τ x = x := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro hx
    exact hx τ (Subgroup.mem_zpowers τ)
  · intro hx f hf
    have hle : Subgroup.zpowers τ ≤ MulAction.stabilizer Gal(L/ℚ) x := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hx
    exact MulAction.mem_stabilizer_iff.1 (hle hf)
end Formalism.FrobeniusOrbits.Galois
