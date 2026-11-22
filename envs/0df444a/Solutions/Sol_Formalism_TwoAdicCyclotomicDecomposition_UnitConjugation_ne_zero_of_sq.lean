-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.ne_zero_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:16:51.375589+00:00
-- url     : https://prove2.me/submissions/bbc50629-f9bc-4936-a3e8-80d9643a89ed

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
theorem _root_.solution (hq : 0 < q) (ha : a ^ 2 = -(q : L)) : a ≠ 0 := by
  intro h0
  rw [h0, zero_pow two_ne_zero, zero_eq_neg] at ha
  exact hq.ne' (by exact_mod_cast ha)
end Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
