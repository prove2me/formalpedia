-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_variation_narrow_winding_interval
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:18.211981+00:00
-- url     : https://prove2.me/submissions/683cf528-97d1-4d4d-a48e-2631c2e0532d

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_width_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (T : ℝ),
    ∃ (ρ θ : ℝ × ℝ → ℝ) (a b : ℝ), Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      (∀ x, convexModelContactVariationPath M q Z x.1 ![Real.cos x.2, Real.sin x.2] =
        ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)]) ∧
      a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      b - a < 1 / 2 ∧
      ((3 : ℤ) ≤ Int.ceil a + Int.ceil b - 1 ↔
        ∀ s ∈ Icc 0 (2 * Real.pi), 2 * Real.pi < θ (T, s) - s) := by
  exact BirkhoffGlobalSection.contact_winding_width_bundle.2.2.2.2.2.2
