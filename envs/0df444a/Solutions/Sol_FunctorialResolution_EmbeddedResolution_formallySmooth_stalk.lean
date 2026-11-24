-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.formallySmooth_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:16:54.072116+00:00
-- url     : https://prove2.me/submissions/c0e3f64e-686a-4c98-8835-fd2e53d375b6

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_formallySmooth_sections
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
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    @Algebra.FormallySmooth k _ _ _ (stalkAlgebra k p x) := by
  obtain ⟨U, hxU, hU⟩ := exists_isAffineOpen_mem X x
  let algU : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let algStalk : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  let algGerm : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have _tower : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    isScalarTower_stalk k p U x hxU rfl rfl rfl
  have _fsU : Algebra.FormallySmooth k Γ(X, U) := formallySmooth_sections k p U hU rfl
  have _loc : IsLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have _fsStalk : Algebra.FormallySmooth Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallySmooth.of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact Algebra.FormallySmooth.comp k Γ(X, U) (X.presheaf.stalk x)
end FunctorialResolution.EmbeddedResolution
