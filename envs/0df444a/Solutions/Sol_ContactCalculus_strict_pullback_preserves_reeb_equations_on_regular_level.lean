-- Prove2me | solution 1 for ContactCalculus.strict_pullback_preserves_reeb_equations_on_regular_level
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T16:11:33.968726+00:00
-- url     : https://prove2.me/submissions/ade5ed21-15ce-4e2f-9b68-897c90ca680c

import Theorems.Thm_ImplicitCalculus_bijective_tangent_map_of_injective_on_regular_levels
import Theorems.Thm_ContactCalculus_extDeriv_naturality_of_tangent_pullback_on_regular_level
import Definitions.Def_GrayStability_Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
open GrayStability
open scoped ContDiff

theorem solution {n c : ℕ} (F : E n → E c) (hF : ContDiff ℝ ∞ F)
    (hreg : ∀ z ∈ levelSet F, Function.Surjective (fderiv ℝ F z))
    (α β : OneForm n) (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (f : E n → E n) (hf : ContDiff ℝ ∞ f)
    (hmap : Set.MapsTo f (levelSet F) (levelSet F))
    (hinj : ∀ z ∈ levelSet F, Set.InjOn (fderiv ℝ f z) (tangentSpace F z))
    (hpull : ∀ z ∈ levelSet F, ∀ v ∈ tangentSpace F z,
      pullback f α z v = β z v)
    (y : E n) (hy : y ∈ levelSet F) (u : E n)
    (hu : u ∈ tangentSpace F y) (hnorm : β y u = 1)
    (hker : ∀ v ∈ tangentSpace F y, extDerivOneForm β y u v = 0) :
    fderiv ℝ f y u ∈ tangentSpace F (f y) ∧
      α (f y) (fderiv ℝ f y u) = 1 ∧
      ∀ w ∈ tangentSpace F (f y),
        extDerivOneForm α (f y) (fderiv ℝ f y u) w = 0 := by
  have hbij := ImplicitCalculus.bijective_tangent_map_of_injective_on_regular_levels
    F F hF (hF.differentiable (by simp)) f (hf.differentiable (by simp))
    hmap y hy (hreg y hy) (hreg (f y) (hmap hy)) (hinj y hy)
  refine ⟨hbij.mapsTo hu, ?_, ?_⟩
  · exact (hpull y hy u hu).trans hnorm
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hbij.surjOn hw
    rw [← hvw]
    exact (ContactCalculus.extDeriv_naturality_of_tangent_pullback_on_regular_level
      F hF hreg α β hα hβ f hf hpull y hy u v hu hv).trans (hker v hv)

