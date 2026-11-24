-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.free_kaehlerDifferential_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:34:17.218035+00:00
-- url     : https://prove2.me/submissions/6fb50d55-f5d1-4cc9-9c7f-133dc13a1d50

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isNoetherianRing_stalk
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_formallySmooth_stalk
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_finite_kaehlerDifferential_stalk
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
private theorem free_kaehlerDifferential_of_formallySmooth (k : Type u) [Field k] (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k A]
    [Module.Finite A (KaehlerDifferential k A)] :
    Module.Free A (KaehlerDifferential k A) := by
  have _h1 : Module.FinitePresentation A (KaehlerDifferential k A) :=
    Module.finitePresentation_of_finite ..
  have _h2 : Module.Projective A (KaehlerDifferential k A) := inferInstance
  have _h3 : Module.Flat A (KaehlerDifferential k A) := inferInstance
  exact Module.free_of_flat_of_isLocalRing
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
    Module.Free (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) := by
  let algst : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
  have _hN : IsNoetherianRing (X.presheaf.stalk x) := isNoetherianRing_stalk k p x
  have _hFS : Algebra.FormallySmooth k (X.presheaf.stalk x) := formallySmooth_stalk k p x
  have _hFin : Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) :=
    finite_kaehlerDifferential_stalk k p x
  exact free_kaehlerDifferential_of_formallySmooth k (X.presheaf.stalk x)
end FunctorialResolution.EmbeddedResolution
