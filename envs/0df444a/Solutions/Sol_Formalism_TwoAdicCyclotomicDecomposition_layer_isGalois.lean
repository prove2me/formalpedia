-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layer_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:50:09.999278+00:00
-- url     : https://prove2.me/submissions/0da6f5f6-9a1a-412d-adc7-15790cd3dfdc

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layer_splitting

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
variable {L : Type} [Field L] [NumberField L] {n q d : ℕ} {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (h : IsLayer n q d ζ a b) : IsGalois ℚ L := by
  have := layer_splitting h
  have := Normal.of_isSplittingField (F := ℚ) (E := L)
    ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)))
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
end Formalism.TwoAdicCyclotomicDecomposition
