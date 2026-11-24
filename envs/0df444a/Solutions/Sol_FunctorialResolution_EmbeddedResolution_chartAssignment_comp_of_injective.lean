-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartAssignment_comp_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:51.213071+00:00
-- url     : https://prove2.me/submissions/c1dfcf71-5808-482e-91ad-21482d626fdd

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {α : Type*}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
    (E E' : List X.IdealSheafData) (σ : ℕ → ℕ)
    (hinj : Function.Injective σ)
    (hlt : ∀ i, i < E'.length → σ i < E.length)
    (hEq : ∀ i, ∀ h : i < E'.length, (E'[i]'h) = E[σ i]'(hlt i h))
    (hainj : ∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤)
    (hsome : ∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
      restrictIdeal (E[i]'h) U = c.coordIdeal {t}) :
    (∀ i < E'.length, ∀ j < E'.length, ∀ t : Fin m,
        (a ∘ σ) i = some t → (a ∘ σ) j = some t → i = j) ∧
      (∀ i, ∀ h : i < E'.length, (a ∘ σ) i = none → restrictIdeal (E'[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E'.length, ∀ t : Fin m, (a ∘ σ) i = some t →
        restrictIdeal (E'[i]'h) U = c.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj t hit hjt
    simp only [Function.comp_apply] at hit hjt
    exact hinj (hainj (σ i) (hlt i hi) (σ j) (hlt j hj) t hit hjt)
  · intro i h hn
    simp only [Function.comp_apply] at hn
    rw [hEq i h]
    exact hnone (σ i) (hlt i h) hn
  · intro i h t ht
    simp only [Function.comp_apply] at ht
    rw [hEq i h]
    exact hsome (σ i) (hlt i h) t ht
end FunctorialResolution.EmbeddedResolution
