-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_positive_time_change_variational_transport
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:14:35.881848+00:00
-- url     : https://prove2.me/submissions/5c15003d-5fba-4427-adc9-b023379b871c

import Theorems.Thm_BirkhoffGlobalSection_positive_time_change_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (b : Phase → ℝ) (x : ℝ → Phase)
    (Y : ℝ → (Phase →L[ℝ] Phase)) (τ : ℝ → ℝ)
    (hx : ∀ s, HasDerivAt x (hamiltonianVectorField F (x s)) s)
    (hY : ∀ s, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField F) (x s)).comp (Y s)) s)
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase) (hτ0 : τ 0 = 0)
    (hτ : ∀ t, HasDerivAt τ (b (x (τ t))) t)
    (hX : ∀ t, DifferentiableAt ℝ (hamiltonianVectorField F) (x (τ t)))
    (hb : ∀ t, DifferentiableAt ℝ b (x (τ t)))
    (hpos : ∀ t, 0 < b (x (τ t)))
    (hk : ∀ v : Phase, Continuous (fun t => fderiv ℝ b (x (τ t)) (Y (τ t) v))),
    ∀ v : Phase, ∃ z : ℝ → Phase,
      z 0 = v ∧
      (∀ t, HasDerivAt z
        (fderiv ℝ (fun y => b y • hamiltonianVectorField F y) (x (τ t)) (z t)) t) ∧
      (∀ t, transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (z t) =
        transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (Y (τ t) v)) := by
  exact BirkhoffGlobalSection.positive_time_change_bundle.{0, 0}.2.2.2.1
