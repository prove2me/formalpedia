-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.length_coker_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:44.030898+00:00
-- url     : https://prove2.me/submissions/40bedf79-6d3a-4595-9f4d-444c3a276699

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_SubmoduleLengthBoundStatement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_QuotLen
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_eq_ker_add_range


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
theorem _root_.solution (a : O) {M : Type u} [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) :
    Module.length O (M ⧸ mulSub a M) = Module.length O (LinearMap.ker (LinearMap.lsmul O M a)) := by
  have h1 := Formalism.NG.IdempotentNormalFormsRhoFacts.length_eq_ker_add_range (LinearMap.lsmul O M a)
  have h2 : Module.length O M = Module.length O (mulSub a M) + Module.length O (M ⧸ mulSub a M) :=
    Module.length_eq_add_of_exact (mulSub a M).subtype (mulSub a M).mkQ
      (mulSub a M).injective_subtype (mulSub a M).mkQ_surjective
      (LinearMap.exact_subtype_mkQ _)
  have hr : Module.length O (mulSub a M) ≠ ⊤ := by
    intro h
    rw [h, top_add] at h2
    exact hM h2
  have h3 : Module.length O (M ⧸ mulSub a M) + Module.length O (mulSub a M) =
      Module.length O (LinearMap.ker (LinearMap.lsmul O M a)) + Module.length O (mulSub a M) := by
    rw [add_comm, ← h2, h1]; rfl
  exact ENat.add_left_injective_of_ne_top hr h3
end Formalism.RepresentationBoundsCohomology.LOC
