-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartEvalHom_comp_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:35.220042+00:00
-- url     : https://prove2.me/submissions/f6e18b84-0d86-4dab-83b3-03fd8ca31431

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}} {W : X.Opens} {V : Y.Opens} {n : Type u}
private theorem resLE_appTop_eq {X' Y' : Scheme.{u}} (h : Y' ⟶ X') (W' : X'.Opens)
    (V' : Y'.Opens) (e : V' ≤ h ⁻¹ᵁ W') :
    (h.resLE W' V' e).appTop = W'.topIso.hom ≫ h.appLE W' V' e ≫ V'.topIso.inv := by
  simp
private theorem resLE_appTop_conj_topIso_eq_appLE {X' Y' : Scheme.{u}} (h : Y' ⟶ X') (W' : X'.Opens) (V' : Y'.Opens)
    (e : V' ≤ h ⁻¹ᵁ W') :
    W'.topIso.inv ≫ (h.resLE W' V' e).appTop ≫ V'.topIso.hom = h.appLE W' V' e := by
  rw [resLE_appTop_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}} {W : X.Opens} {V : Y.Opens} {n : Type u}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (hW : IsAffineOpen W) (h : Y ⟶ X) (e : V ≤ h ⁻¹ᵁ W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme)
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) :
    (chartEvalHom hW g).comp (MvPolynomial.C : Γ(X, W) →+* MvPolynomial n Γ(X, W)) =
      (h.appLE W V e).hom := by
  have key : chartCoeffHom g = (h.appLE W V e).hom := by
    simp only [chartCoeffHom, hg, resLE_appTop_conj_topIso_eq_appLE]
  refine RingHom.ext fun a => ?_
  have h1 : chartEvalHom hW g (MvPolynomial.C a) = chartCoeffHom g a := by simp [chartEvalHom]
  rw [RingHom.comp_apply, h1, key]
end FunctorialResolution.EmbeddedResolution
