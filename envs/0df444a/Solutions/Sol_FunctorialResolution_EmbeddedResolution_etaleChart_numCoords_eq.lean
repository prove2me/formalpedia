-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.etaleChart_numCoords_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:02:02.220048+00:00
-- url     : https://prove2.me/submissions/f4876f64-e8a4-42a9-a0b2-6eb0a3f0091c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebra_formallyEtale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_isScalarTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal



set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) {m m' : ℕ} (c : EtaleChart p U m) (c' : EtaleChart p U m') : m = m' := by
  let instk : Algebra k Γ(X, U) := sectionsAlgebra k p U
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  let instc' : Algebra (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) := c'.algebra
  have instt : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
    c.isScalarTower
  have instt' : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) :=
    c'.isScalarTower
  have instfe : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) :=
    c.algebra_formallyEtale hU
  have instfe' : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m')) k) Γ(X, U) :=
    c'.algebra_formallyEtale hU
  have instnt : Nontrivial Γ(X, U) :=
    RingHom.domain_nontrivial (X.presheaf.germ U x hx).hom
  have h1 : Module.finrank Γ(X, U) (KaehlerDifferential k Γ(X, U))
      = Fintype.card (ULift.{u} (Fin m)) :=
    Module.finrank_eq_card_basis (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m)) Γ(X, U))
  have h2 : Module.finrank Γ(X, U) (KaehlerDifferential k Γ(X, U))
      = Fintype.card (ULift.{u} (Fin m')) :=
    Module.finrank_eq_card_basis (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin m')) Γ(X, U))
  have h3 : Fintype.card (ULift.{u} (Fin m)) = Fintype.card (ULift.{u} (Fin m')) :=
    h1.symm.trans h2
  simpa using h3
end FunctorialResolution.EmbeddedResolution
