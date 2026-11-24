-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.length_quot_le_of_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:46.801802+00:00
-- url     : https://prove2.me/submissions/64f75eb3-8272-4a23-901a-a5ec02c9f060

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_SubmoduleLengthBoundStatement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_QuotLen
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_mem_mulSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
variable {O : Type u} [CommRing O]
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution {a : O} {M M' : Type u} [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M') (hf : Function.Surjective f) :
    Module.length O (M' ⧸ mulSub a M') ≤ Module.length O (M ⧸ mulSub a M) := by
  have hle : mulSub a M ≤ (mulSub a M').comap f := by
    intro x hx
    obtain ⟨m, rfl⟩ := (mem_mulSub x).1 hx
    exact (mem_mulSub _).2 ⟨f m, by rw [map_smul]⟩
  refine Module.length_le_of_surjective (Submodule.mapQ _ _ f hle) ?_
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk x, rfl⟩
end Formalism.RepresentationBoundsCohomology.LOC
