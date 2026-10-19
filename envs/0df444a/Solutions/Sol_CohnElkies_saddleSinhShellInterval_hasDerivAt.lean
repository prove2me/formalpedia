-- Prove2me | solution 1 for CohnElkies.saddleSinhShellInterval_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/b4d6af9b-271b-477c-9480-b87df600c5c5

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ => ∫ x in a..b,
        w x * x * Real.sinh (x * v))
      (∫ x in a..b,
        w x * x ^ 2 * Real.cosh (x * u)) u := by
  let F : ℝ → ℝ → ℝ := fun v x =>
    w x * x * Real.sinh (x * v)
  let F' : ℝ → ℝ → ℝ := fun v x =>
    w x * x ^ 2 * Real.cosh (x * v)
  have hF (v : ℝ) : Continuous (F v) := by
    try dsimp [F]
    exact (hw.mul continuous_id).mul
      (Real.continuous_sinh.comp
        (continuous_id.mul continuous_const))
  have hF' (v : ℝ) : Continuous (F' v) := by
    try dsimp [F']
    exact (hw.mul (continuous_id.pow 2)).mul
      (Real.continuous_cosh.comp
        (continuous_id.mul continuous_const))
  have hF'joint : Continuous (Function.uncurry F') := by
    try dsimp [F', Function.uncurry]
    exact ((hw.comp continuous_snd).mul
      (continuous_snd.pow 2)).mul
        (Real.continuous_cosh.comp
          (continuous_snd.mul continuous_fst))
  have hderiv (x v : ℝ) :
      HasDerivAt (fun z : ℝ => F z x) (F' v x) v := by
    have hlinear : HasDerivAt
        (fun z : ℝ => x * z) x v := by
      simpa using! (hasDerivAt_id v).const_mul x
    have hsinh := (Real.hasDerivAt_sinh
      (x * v)).comp v hlinear
    simpa [F, F', pow_two, mul_assoc, mul_left_comm, mul_comm] using! hsinh.const_mul (w x * x)
  have hrewrite :
      (fun v : ℝ => ∫ x in a..b,
        w x * x * Real.sinh (x * v)) =
      (fun v : ℝ => ∫ x in Set.Icc a b, F v x) := by
    funext v
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  have hderivrewrite :
      (∫ x in a..b,
        w x * x ^ 2 * Real.cosh (x * u)) =
      (∫ x in Set.Icc a b, F' u x) := by
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  rw [hrewrite, hderivrewrite]
  have hcompact :
      IsCompact (Metric.closedBall u 1 ×ˢ Set.Icc a b) :=
    (isCompact_closedBall u 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ :=
    hcompact.bddAbove_image hF'joint.norm.continuousOn
  have hbound : ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      ∀ v ∈ Metric.ball u 1, ‖F' v x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc]
      with x hx
    intro v hv
    have hpair :
        (v, x) ∈ Metric.closedBall u 1 ×ˢ Set.Icc a b :=
      ⟨Metric.ball_subset_closedBall hv, hx⟩
    exact hC (Set.mem_image_of_mem
      (fun p : ℝ × ℝ => ‖F' p.1 p.2‖) hpair)
  have hmeas : ∀ᶠ v in 𝓝 u,
      AEStronglyMeasurable (F v)
        (volume.restrict (Set.Icc a b)) :=
    Eventually.of_forall
      (fun v => (hF v).aestronglyMeasurable)
  have hint : Integrable (F u)
      (volume.restrict (Set.Icc a b)) :=
    (hF u).integrableOn_Icc
  have hderivmeas : AEStronglyMeasurable (F' u)
      (volume.restrict (Set.Icc a b)) :=
    (hF' u).aestronglyMeasurable
  have hconstant : Integrable (fun _ : ℝ => C)
      (volume.restrict (Set.Icc a b)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hdifferentiable :
      ∀ᵐ x ∂volume.restrict (Set.Icc a b),
        ∀ v ∈ Metric.ball u 1,
          HasDerivAt (fun z : ℝ => F z x) (F' v x) v :=
    Eventually.of_forall (fun x v _ => hderiv x v)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc a b))
    (s := Metric.ball u 1) (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds u zero_lt_one)
    hmeas hint hderivmeas hbound hconstant
    hdifferentiable).2
end CohnElkies
