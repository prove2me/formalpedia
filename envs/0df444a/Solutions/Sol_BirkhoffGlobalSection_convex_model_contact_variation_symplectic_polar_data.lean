-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_variation_symplectic_polar_data
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:01:10.549543+00:00
-- url     : https://prove2.me/submissions/ca43e4e1-bfd5-4e68-8427-1a927beb3a81

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
import Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false

set_option linter.unusedVariables false in
private theorem convex_model_contact_variation_path_area_preserved : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p r : Plane),
    convexModelContactVariationPath M q Z t p 0 * convexModelContactVariationPath M q Z t r 1 -
      convexModelContactVariationPath M q Z t p 1 * convexModelContactVariationPath M q Z t r 0 =
      p 0 * r 1 - p 1 * r 0 := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem convex_model_contact_variation_path_bijective : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ),
    Function.Bijective (convexModelContactVariationPath M q Z t) := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.2.2.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem convex_model_contact_variation_polar_lift : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane) (hp : p ≠ 0),
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      ∀ t, convexModelContactVariationPath M q Z t p =
        ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)] := by
  exact BirkhoffGlobalSection.contact_angular_lift_bundle.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem plane_polar_increment_unique : ∀ (v : ℝ → Plane) (ρ σ θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ t, 0 < ρ t) (hσ : ∀ t, 0 < σ t)
    (hvθ : ∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)])
    (hvψ : ∀ t, v t = ![σ t * Real.cos (ψ t), σ t * Real.sin (ψ t)]),
    ∀ t, θ t - θ 0 = ψ t - ψ 0 := by
  exact BirkhoffGlobalSection.contact_angular_lift_bundle.2.2.2.2.1

theorem solution {μ c : ℝ} (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) :
    let A := convexModelContactVariationPath M q Z
    (∀ p r : Plane, ∀ t, A t p 0 * A t r 1 - A t p 1 * A t r 0 = p 0 * r 1 - p 1 * r 0) ∧
    (∀ t, Function.Bijective (A t)) ∧ (∀ p, A 0 p = p) ∧
    (∀ p, Continuous (fun t => A t p)) ∧
    ∀ p : Plane, p ≠ 0 → ∃ ρ θ : ℝ → ℝ,
      Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      (∀ t, A t p = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧
      ∀ ψ : ℝ → ℝ, Continuous ψ →
        (∀ t, ∃ σ : ℝ, 0 < σ ∧ A t p = ![σ * Real.cos (ψ t), σ * Real.sin (ψ t)]) →
        ∀ t, θ t - θ 0 = ψ t - ψ 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p r t
    exact convex_model_contact_variation_path_area_preserved M q Z hs hq hZ hZ0 t p r
  · exact fun t => convex_model_contact_variation_path_bijective M q Z hs hq hZ hZ0 t
  · exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.2.1 M q Z (hs 0) hZ0
  · intro p
    exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.2.2.1
      M q Z hs (continuous_iff_continuousAt.mpr (fun t => (hq t).continuousAt))
      (continuous_iff_continuousAt.mpr (fun t => (hZ t).continuousAt)) p
  · intro p hp
    obtain ⟨ρ, θ, hρ, hθ, hpos, he⟩ := convex_model_contact_variation_polar_lift M q Z hs hq hZ hZ0 p hp
    refine ⟨ρ, θ, hρ, hθ, hpos, he, ?_⟩
    intro ψ hψ hpolar
    classical
    choose σ hσ hσeq using hpolar
    exact plane_polar_increment_unique _ ρ σ θ ψ hθ hψ hpos hσ he hσeq
