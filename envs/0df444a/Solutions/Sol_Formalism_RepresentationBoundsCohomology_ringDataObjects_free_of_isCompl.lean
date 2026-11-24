-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.free_of_isCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:41.316261+00:00
-- url     : https://prove2.me/submissions/afcb233a-7a9f-4e71-81fb-d35df608ba89

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution [IsLocalRing O] (p q : Submodule O (r → O)) (h : IsCompl p q) :
    Module.Free O p ∧ Module.Finite O p := by
  have hsurj : Function.Surjective (Submodule.linearProjOfIsCompl p q h) :=
    fun x => ⟨(x : r → O), Submodule.linearProjOfIsCompl_apply_left h x⟩
  have hfin : Module.Finite O p := Module.Finite.of_surjective _ hsurj
  haveI : Module.Projective O p :=
    Module.Projective.of_split p.subtype (Submodule.linearProjOfIsCompl p q h)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)
  haveI : Module.FinitePresentation O p := by
    first
    | infer_instance
    | exact Module.finitePresentation_of_projective _ _
    | exact Module.finitePresentation_of_projective
  exact ⟨Module.free_of_flat_of_isLocalRing, hfin⟩
end Formalism.RepresentationBoundsCohomology.ringDataObjects
