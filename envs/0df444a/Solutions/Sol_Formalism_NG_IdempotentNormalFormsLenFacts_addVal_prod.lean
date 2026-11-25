-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.addVal_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:27:20.81439+00:00
-- url     : https://prove2.me/submissions/dfb154f1-3a03-41d9-9076-5ad94fe91abd

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Theorems.Thm_Bl_AddValuationProducts_goal1
import Theorems.Thm_Bl_SecondBlockLemmaA_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentNormalFormsLenFacts
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.NG.IdempotentNormalFormsLenFacts
theorem _root_.solution {ι : Type*} (s : Finset ι) (a : ι → O) :
    addVal O (∏ i ∈ s, a i) = ∑ i ∈ s, addVal O (a i) := by
  first | exact Bl.SecondBlockLemmaA.goal1 .. | (apply Bl.SecondBlockLemmaA.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaA.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaA.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaA.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaA.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› ι s a | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› ι s | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› ι | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› | exact @Bl.SecondBlockLemmaA.goal1 O
end Formalism.NG.IdempotentNormalFormsLenFacts
