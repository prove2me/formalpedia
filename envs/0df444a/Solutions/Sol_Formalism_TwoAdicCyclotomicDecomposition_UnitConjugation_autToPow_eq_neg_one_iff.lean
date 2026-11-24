-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.autToPow_eq_neg_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:09.569384+00:00
-- url     : https://prove2.me/submissions/123a33fe-731a-44e1-9fb2-ebeb8dfdc278

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_pow_eq_inv_iff

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
variable {n q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
theorem _root_.solution (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    hζ.autToPow ℚ σ = -1 ↔ σ ζ = ζ⁻¹ := by
  rw [← hζ.autToPow_spec ℚ σ, pow_eq_inv_iff hζ, ZMod.natCast_val, ZMod.cast_id, Units.ext_iff,
    Units.val_neg, Units.val_one]
end Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
