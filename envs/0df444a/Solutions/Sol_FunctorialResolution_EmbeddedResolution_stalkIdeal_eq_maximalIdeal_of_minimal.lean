-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_eq_maximalIdeal_of_minimal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:34.472049+00:00
-- url     : https://prove2.me/submissions/d73b84ab-9aa7-4789-b821-54e78d3af19c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_span_germ_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_primeIdealOf_eq_comap_span_germ_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_ne_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (x η : X) (_hx : x ∈ V) (hη : η ∈ V)
    (_hspec : η ⤳ x) (hηs : η ∈ D.support)
    (hmin : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal → P = (hV.primeIdealOf ⟨η, hη⟩).asIdeal) :
    stalkIdeal D η = IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk η) :=
    (X.presheaf.germ V η hη).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk η)
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal := hV.isLocalization_stalk ⟨η, hη⟩
  have halg : (algebraMap (Γ(X, V)) (X.presheaf.stalk η)) = (X.presheaf.germ V η hη).hom := rfl
  have hsp : stalkIdeal D η =
      Ideal.span ({(X.presheaf.germ V η hη).hom (c.coord j)} : Set (X.presheaf.stalk η)) :=
    stalkIdeal_eq_span_germ_coord p hV c j D hD η hη
  have hpeq : (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (X.presheaf.germ V η hη).hom
        (Ideal.span ({(X.presheaf.germ V η hη).hom (c.coord j)} :
          Set (X.presheaf.stalk η))) :=
    primeIdealOf_eq_comap_span_germ_coord p hV c j D hD η η hη hη specializes_rfl hηs hmin
  have hne : stalkIdeal D η ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top D η).mp hηs
  have hsub : Ideal.comap (X.presheaf.germ V η hη).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk η)) ≤
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal := by
    intro a ha
    by_contra hcon
    have hunit : IsUnit ((X.presheaf.germ V η hη).hom a) :=
      IsLocalization.map_units (S := X.presheaf.stalk η)
        (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl) ⟨a, hcon⟩
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
    exact ha hunit
  have h1 : Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
      (Ideal.comap (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η)))
      = IsLocalRing.maximalIdeal (X.presheaf.stalk η) :=
    IsLocalization.map_under (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl)
      (S := X.presheaf.stalk η) _
  refine le_antisymm (IsLocalRing.le_maximalIdeal hne) ?_
  rw [hsp, ← h1, Ideal.map_le_iff_le_comap, halg]
  exact le_trans hsub (le_of_eq hpeq)
end FunctorialResolution.EmbeddedResolution
