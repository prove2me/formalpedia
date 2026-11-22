-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.two_intCast_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:41.166442+00:00
-- url     : https://prove2.me/submissions/22b1c94e-e269-4bf1-ba4c-7967dbf2ccbc

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
theorem _root_.solution {L : Type} [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.LiesOver (span {(2 : ℤ)})] (m : ℤ) :
    (m : 𝓞 L) ∈ P ↔ (2 : ℤ) ∣ m := by
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (span {(2 : ℤ)}), Ideal.under_def,
    Ideal.mem_comap, eq_intCast]
end Formalism.TwoAdicCyclotomicDecomposition
