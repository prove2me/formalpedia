-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.galMap_eq_JJ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:31.240914+00:00
-- url     : https://prove2.me/submissions/a050824c-06b8-44d8-b0c6-331bdb2aa53d

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
variable {n q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
theorem _root_.solution (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    galMap hζ a b σ = JJ n ↔ hζ.autToPow ℚ σ = -1 ∧ sgn σ a = -1 ∧ sgn σ b = -1 := by
  simp only [galMap, JJ, Prod.mk.injEq]
end Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
