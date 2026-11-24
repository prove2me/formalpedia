-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.comap_reducedInverseImage_chartToLastObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:47:17.607688+00:00
-- url     : https://prove2.me/submissions/d74a005d-e6e9-4ae4-9251-e4c12921d15f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionStrictNormalCrossings
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_chartToLastObj_preimage_smoothLocusComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
namespace LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
private theorem support_vanishingIdeal_eq {Y : Scheme.{u}} (Z : Closeds ↥Y) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl
private theorem comap_vanishingIdeal_of_isOpenImmersion {Y T : Scheme.{u}} (g : T ⟶ Y)
    [IsOpenImmersion g] (Z : Closeds ↥Y) (W : Closeds ↥T)
    (hW : (W : Set ↥T) = g.base ⁻¹' (Z : Set ↥Y)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap g
      = Scheme.IdealSheafData.vanishingIdeal W := by
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap g).radical
      = (Scheme.IdealSheafData.vanishingIdeal Z).comap g := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    rw [Scheme.IdealSheafData.radical_ideal,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact ((PrimeSpectrum.isRadical_vanishingIdeal _).comap _).radical
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap g).support = W := by
    rw [Scheme.IdealSheafData.support_comap, support_vanishingIdeal_eq]
    exact TopologicalSpace.Closeds.ext hW.symm
  rw [← hsupp, Scheme.IdealSheafData.vanishingIdeal_support, hrad]
end LocalResolutionData
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
namespace FunctorialResolution.EmbeddedResolution.LocalResolutionData
theorem _root_.solution (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (reducedInverseImage s.lastStructMap (smoothLocusComplement f)).comap (d.chartToLastObj i)
      = reducedInverseImage (d.seq i).lastStructMap (smoothLocusComplement (d.cover.f i ≫ f)) := by
  have h1 := d.chartToLastObj_preimage_smoothLocusComplement i
  unfold reducedInverseImage
  exact comap_vanishingIdeal_of_isOpenImmersion (d.chartToLastObj i) _ _ h1.symm
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
