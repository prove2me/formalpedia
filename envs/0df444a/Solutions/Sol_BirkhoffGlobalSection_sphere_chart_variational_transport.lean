-- Prove2me | solution 1 for BirkhoffGlobalSection.sphere_chart_variational_transport
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:16:01.272989+00:00
-- url     : https://prove2.me/submissions/50ad1a35-56d7-47b6-9016-dbc7186f7efe

import Theorems.Thm_BirkhoffGlobalSection_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (f R X : Phase → Phase) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hvS : ∀ t, q t 0 * v t 0 + q t 1 * v t 1 +
      q t 2 * v t 2 + q t 3 * v t 3 = 0)
    (hf : ∀ t, ContDiffAt ℝ ∞ f (q t))
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (hX : ∀ t, DifferentiableAt ℝ X (f (q t)))
    (hpush : ∀ z ∈ unitThreeSphere, fderiv ℝ f z (R z) = X (f z))
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t),
    (∀ t, HasDerivAt (fun s => f (q s)) (X (f (q t))) t) ∧
    (∀ t, HasDerivAt (fun s => fderiv ℝ f (q s) (v s))
      (fderiv ℝ X (f (q t)) (fderiv ℝ f (q t) (v t))) t) := by
  exact BirkhoffGlobalSection.radial_variation_bundle.2.2.2.2.1
