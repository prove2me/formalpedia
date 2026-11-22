-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.pm_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:37.278298+00:00
-- url     : https://prove2.me/submissions/92b6e641-4655-4308-8417-1d482df6822b

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
theorem _root_.solution {x : L} {c : ℕ} (hx : x ^ 2 = -(c : L)) (σ : Gal(L/ℚ)) :
    σ x = x ∨ σ x = -x := by
  have : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_neg, map_natCast]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this
end Formalism.TwoAdicCyclotomicDecomposition
