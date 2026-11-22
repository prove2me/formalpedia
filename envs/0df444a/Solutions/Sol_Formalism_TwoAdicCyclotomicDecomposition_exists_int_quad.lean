-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.exists_int_quad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:32.337835+00:00
-- url     : https://prove2.me/submissions/5e660fc9-6404-4ecf-b35b-dcae001cb5fd

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Theorems.Thm_Bl_FirstBlockLemmaE_goal1
import Theorems.Thm_Bl_general_b_fact_right_ter_form_goal1


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
theorem _root_.solution {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ)
    (hx : x ^ 2 = x + c) : ∃ X : 𝓞 L, (X : L) = x ∧ X ^ 2 = X + (c : 𝓞 L) := by
  first | exact Bl.FirstBlockLemmaE.goal1 .. | (apply Bl.FirstBlockLemmaE.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaE.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaE.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaE.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaE.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaE.goal1 L ‹_› ‹_› x c hx | exact @Bl.FirstBlockLemmaE.goal1 L ‹_› ‹_› x c | exact @Bl.FirstBlockLemmaE.goal1 L ‹_› ‹_› x | exact @Bl.FirstBlockLemmaE.goal1 L ‹_› ‹_› | exact @Bl.FirstBlockLemmaE.goal1 L ‹_› | exact @Bl.FirstBlockLemmaE.goal1 L
end Formalism.TwoAdicCyclotomicDecomposition
