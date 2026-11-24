-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.pow_eq_inv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:31.894664+00:00
-- url     : https://prove2.me/submissions/702a90e1-9277-408c-a403-45ba75593eb7

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
namespace Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
theorem _root_.solution {K : Type*} [Field K] {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (k : ℕ) : ζ ^ k = ζ⁻¹ ↔ (k : ZMod m) = -1 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne m)
  have e : ζ ^ k = ζ⁻¹ ↔ ζ ^ k * ζ = 1 :=
    ⟨fun h => by rw [h, inv_mul_cancel₀ hζ0], fun h => eq_inv_of_mul_eq_one_left h⟩
  rw [e, ← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
  push_cast
  exact add_eq_zero_iff_eq_neg
end Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
