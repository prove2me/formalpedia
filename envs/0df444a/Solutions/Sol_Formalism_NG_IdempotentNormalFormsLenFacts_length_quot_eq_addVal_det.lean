-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_eq_addVal_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:50.540836+00:00
-- url     : https://prove2.me/submissions/aeeb439c-6472-4260-a471-eb959e89136e

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Submodule O (ι → O)) (e : (ι → O) ≃ₗ[O] N) :
    Module.length O ((ι → O) ⧸ N) =
      addVal O (LinearMap.det (N.subtype ∘ₗ (e : (ι → O) →ₗ[O] N))) := by
  first | exact Bl.AddValuationProducts.goal1 .. | (apply Bl.AddValuationProducts.goal1 <;> assumption) | (intros; apply Bl.AddValuationProducts.goal1 <;> assumption) | (apply @Bl.AddValuationProducts.goal1 <;> assumption) | (intros; apply @Bl.AddValuationProducts.goal1 <;> assumption) | (apply @Bl.AddValuationProducts.goal1 <;> first | assumption | infer_instance) | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› ‹_› N e | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› ‹_› N | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› | exact @Bl.AddValuationProducts.goal1 O
end Formalism.NG.IdempotentNormalFormsLenFacts
