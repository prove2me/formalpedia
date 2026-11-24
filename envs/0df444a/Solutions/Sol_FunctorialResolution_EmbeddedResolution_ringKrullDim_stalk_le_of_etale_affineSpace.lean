-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ringKrullDim_stalk_le_of_etale_affineSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:03:59.54271+00:00
-- url     : https://prove2.me/submissions/6e4379e5-ce01-4707-b3dd-3d2cae3bf2bf

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_AffineSpaceJacobson
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StalkKrullDimension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_stalk_le_topologicalKrullDim
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_stalk_le_of_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_stalk_affineSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map


section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem topologicalKrullDim_spec_le_ringKrullDim (R : CommRingCat.{u}) :
    topologicalKrullDim ↥(Spec R) ≤ ringKrullDim ↥R := by
  have h : topologicalKrullDim (PrimeSpectrum ↥R) = ringKrullDim ↥R :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim ↥R
  exact le_of_eq h
private theorem topologicalKrullDim_affineSpace_le_ringKrullDim (k : Type u) [Field k] (m : ℕ) :
    topologicalKrullDim ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) ≤
      ringKrullDim (MvPolynomial (ULift.{u} (Fin m)) k) := by
  let e := Scheme.homeoOfIso (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k))
  have h3 := (Homeomorph.isEmbedding e).toIsInducing.topologicalKrullDim_le
  exact h3.trans
    (topologicalKrullDim_spec_le_ringKrullDim
      (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)))
private theorem ringKrullDim_mvPolynomial_uLift_le (k : Type u) [Field k] (m : ℕ) :
    ringKrullDim (MvPolynomial (ULift.{u} (Fin m)) k) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have he : ringKrullDim (MvPolynomial (ULift.{u} (Fin m)) k)
      = ringKrullDim (MvPolynomial (Fin m) k) :=
    ringKrullDim_eq_of_ringEquiv
      (MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin m) ≃ Fin m)).toRingEquiv
  rw [he]
  simp
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k : Type u} [Field k] {m : ℕ} {Y : Scheme.{u}}
    (c : Y ⟶ AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k)))
    [AlgebraicGeometry.Etale c] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)] :
    ringKrullDim (Y.presheaf.stalk y) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have hreg : _root_.IsRegularLocalRing
      ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk (c.base y)) :=
    isRegularLocalRing_stalk_affineSpace k (ULift.{u} (Fin m)) (c.base y)
  have h1 : ringKrullDim (Y.presheaf.stalk y) ≤
      ringKrullDim ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk
        (c.base y)) := ringKrullDim_stalk_le_of_etale c y
  have h2 := ringKrullDim_stalk_le_topologicalKrullDim
      (AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) (c.base y)
  exact h1.trans (h2.trans ((topologicalKrullDim_affineSpace_le_ringKrullDim k m).trans
    (ringKrullDim_mvPolynomial_uLift_le k m)))
end FunctorialResolution.EmbeddedResolution
