-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.lastObjIsoPullback_hom_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:01:22.234083+00:00
-- url     : https://prove2.me/submissions/6c9e4a5a-54be-4d88-8efc-7a08a19260f1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_schemeAtIsoOfEq_hom_projectionToBase
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_schemeAtIsoPullback_hom_fst
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_lastStructMap_eq_projectionToBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
variable {X : Scheme.{u}}
end
attribute [instance] LocalResolutionData.finiteType
namespace LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
private theorem eqToHom_comp_pullback_fst {X₀ X₁ Y₀ Y₁ : Scheme.{u}} (φ : X₁ ⟶ X₀)
    {g : Y₀ ⟶ X₀} {g' : Y₁ ⟶ X₀} (hY : Y₀ = Y₁) (hg : eqToHom hY ≫ g' = g)
    (e : (pullback φ g : Scheme.{u}) = (pullback φ g' : Scheme.{u})) :
    eqToHom e ≫ pullback.fst φ g' = pullback.fst φ g := by
  subst hY
  simp only [eqToHom_refl, Category.id_comp] at hg
  subst hg
  simp
end LocalResolutionData
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
attribute [instance] LocalResolutionData.finiteType
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
namespace FunctorialResolution.EmbeddedResolution.LocalResolutionData
theorem _root_.solution (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (d.lastObjIsoPullback i).hom ≫ pullback.fst (d.cover.f i) s.lastStructMap = (d.seq i).lastStructMap := by
  have hg : eqToHom (congrArg s.schemeAt (d.reindex_length i)) ≫ s.lastStructMap
      = s.projectionToBase (d.reindex i (d.seq i).length) := by
    rw [s.lastStructMap_eq_projectionToBase]
    exact s.schemeAtIsoOfEq_hom_projectionToBase (d.reindex_length i)
  have key := eqToHom_comp_pullback_fst (d.cover.f i)
    (congrArg s.schemeAt (d.reindex_length i)) hg (d.pullback_projectionToBase_eq_pullback_lastStructMap i)
  have e1 : (d.lastObjIsoPullback i).hom
      = (d.schemeAtIsoPullback i (d.seq i).length le_rfl).hom ≫ eqToHom (d.pullback_projectionToBase_eq_pullback_lastStructMap i) := rfl
  rw [e1, Category.assoc, key, d.schemeAtIsoPullback_hom_fst i (d.seq i).length le_rfl,
    (d.seq i).lastStructMap_eq_projectionToBase]
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
