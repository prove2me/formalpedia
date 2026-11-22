-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.sgn_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:55.842811+00:00
-- url     : https://prove2.me/submissions/fcbefbff-f18a-4172-b944-f789278852b3

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
theorem _root_.solution {L : Type} [Field L] [Algebra ℚ L] (σ : Gal(L/ℚ)) (x : L) :
    sgn σ x = 1 ↔ σ x = x := by
  unfold sgn
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide
end Formalism.TwoAdicCyclotomicDecomposition
