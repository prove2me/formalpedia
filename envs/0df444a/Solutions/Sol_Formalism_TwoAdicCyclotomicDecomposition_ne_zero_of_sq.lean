-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ne_zero_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:37.910382+00:00
-- url     : https://prove2.me/submissions/61f01b9f-4d4c-4c78-b7bd-e922fc30b8f0

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {x : L} {c : ℕ} (hc : c ≠ 0) (hx : x ^ 2 = -(c : L)) : x ≠ 0 := by
  rintro rfl
  have : (c : L) = 0 := by
    have := hx.symm
    simpa using this
  exact hc (by exact_mod_cast this)
end Formalism.TwoAdicCyclotomicDecomposition
