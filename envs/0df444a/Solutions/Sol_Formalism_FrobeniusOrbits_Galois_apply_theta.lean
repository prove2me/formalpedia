-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.apply_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:17.76237+00:00
-- url     : https://prove2.me/submissions/1c56476f-0ef3-4a2c-b9f4-785e6ae9cbcd

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
theorem _root_.solution {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) (τ : Gal(L/ℚ)) :
    τ (ζ + ζ⁻¹) = ζ ^ (hζ.autToPow ℚ τ : ZMod N).val + ζ⁻¹ ^ (hζ.autToPow ℚ τ : ZMod N).val := by
  rw [map_add, map_inv₀, ← hζ.autToPow_spec ℚ τ, inv_pow]
end Formalism.FrobeniusOrbits.Galois
