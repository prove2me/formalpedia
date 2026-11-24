-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.finite_kaehlerDifferential_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:16:52.734201+00:00
-- url     : https://prove2.me/submissions/dd7feaed-566a-4654-b1b9-3f8c27f88c04

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isScalarTower_stalk
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_isAffineOpen_mem (X : Scheme.{u}) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U :=
  ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, X.affineCover.covers x,
    isAffineOpen_opensRange _⟩
private theorem finite_kaehlerDifferential_of_isLocalization (k A B : Type u) [CommRing k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (M : Submonoid A) [IsLocalization M B]
    (hfin : Module.Finite A (KaehlerDifferential k A)) :
    Module.Finite B (KaehlerDifferential k B) := by
  have := hfin
  have : IsLocalizedModule M (KaehlerDifferential.map k k A B) := inferInstance
  have hbc : IsBaseChange B (KaehlerDifferential.map k k A B) :=
    IsLocalizedModule.isBaseChange M B (KaehlerDifferential.map k k A B)
  have : Module.Finite B (TensorProduct A B (KaehlerDifferential k A)) := inferInstance
  exact Module.Finite.equiv hbc.equiv
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    letI := stalkAlgebra k p x
    Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) := by
  let algStalk : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  show Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x))
  obtain ⟨U, hxU, hUaff⟩ := exists_isAffineOpen_mem X x
  let algSections : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let algGerm : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU rfl rfl rfl
  have : IsLocalization (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hUaff.isLocalization_stalk ⟨x, hxU⟩
  have : Module.FinitePresentation Γ(X, U) (KaehlerDifferential k Γ(X, U)) :=
    finitePresentation_kaehlerDifferential_sections k p ⟨U, hUaff⟩ rfl
  exact finite_kaehlerDifferential_of_isLocalization k Γ(X, U) (X.presheaf.stalk x)
    (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl inferInstance
end FunctorialResolution.EmbeddedResolution
