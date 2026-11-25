-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_sections_span_eq_maximalIdeal_with_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:55.190522+00:00
-- url     : https://prove2.me/submissions/b13146c8-755e-4fb2-bd40-ef6d44a731df

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_GermRegularParameters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_maximalIdeal_iff
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebra_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_regularSystemOfParameters_containing_etaleChartCoords
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
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, X.presheaf.germ U x hx (c.coord j) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ (d : ℕ) (f : Fin d → Γ(X, U)),
      (∀ i, X.presheaf.germ U x hx (f i) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      Ideal.span (Set.range fun i => X.presheaf.germ U x hx (f i)) =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      (d : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) := by
  let instAlg : Algebra (CoordPolynomialRing k m) Γ(X, U) := c.algebra
  have instEt : Algebra.Etale (CoordPolynomialRing k m) Γ(X, U) := c.algebra_etale hU
  let instSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLoc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ t : Γ(X, U),
      algebraMap Γ(X, U) (X.presheaf.stalk x) t = X.presheaf.germ U x hx t := fun _ => rfl
  have hcoord : ∀ j : Fin m, etaleChartCoord k m Γ(X, U) j = c.coord j := by
    intro j
    show c.coordRingHom (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) = c.coord j
    exact c.coordRingHom_X j
  have hq : ∀ j ∈ J₀, etaleChartCoord k m Γ(X, U) j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro j hj
    rw [hcoord j]
    exact (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mp (hJ₀ j hj)
  obtain ⟨d, f, hf1, hf2, hf3, hf4⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m Γ(X, U)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x) J₀ hq
  refine ⟨d, f, ?_, ?_, ?_, hf4⟩
  · intro i
    exact (germ_mem_maximalIdeal_iff hU x hx (f i)).mpr (hf1 i)
  · intro j hj
    obtain ⟨i, hi⟩ := hf2 j hj
    exact ⟨i, by rw [hi, hcoord j]⟩
  · simpa only [halg] using hf3
end FunctorialResolution.EmbeddedResolution
