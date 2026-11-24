-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.gal_sq_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:22.752262+00:00
-- url     : https://prove2.me/submissions/5bfeac7c-6e44-4a5e-a21d-ebe06911b2c5

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {L : Type} [Field L] [Algebra ℚ L] (σ : Gal(L/ℚ)) (x : L) (m : ℤ)
    (hx : x ^ 2 = (m : L)) : σ x = x ∨ σ x = -x := by
  have : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this
end Formalism.TwoAdicCyclotomicDecomposition
