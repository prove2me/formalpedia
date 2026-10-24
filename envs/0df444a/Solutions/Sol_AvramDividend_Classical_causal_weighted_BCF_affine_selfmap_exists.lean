-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_affine_selfmap_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:09:14.248162+00:00
-- url     : https://prove2.me/submissions/db3a5150-3994-4651-809c-81df65349932

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_full_kernel_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_affine_pointwise_bound
import Theorems.Thm_AvramDividend_Classical_causal_BCF_lift_of_nonnegative_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The weighted affine causal map has a BCF-valued realisation. -/
theorem solution
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    ∃ T : BoundedContinuousFunction ℝ≥0 ℝ →
      BoundedContinuousFunction ℝ≥0 ℝ,
      ∀ (f : BoundedContinuousFunction ℝ≥0 ℝ)
        (x : ℝ) (hx : 0 ≤ x),
        T f ⟨x, hx⟩ =
          (Real.exp (-(w * x)) *
            (1 - ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
              (Real.exp (w * s) *
                f ⟨max s 0, le_max_right s 0⟩) ∂volume)) / a := by
  classical
  let F : BoundedContinuousFunction ℝ≥0 ℝ → ℝ → ℝ :=
    fun f x => (Real.exp (-(w * x)) *
      (1 - ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
        (Real.exp (w * s) *
          f ⟨max s 0, le_max_right s 0⟩) ∂volume)) / a
  have hC (f : BoundedContinuousFunction ℝ≥0 ℝ) :
      ContinuousOn (F f) (Ici (0 : ℝ)) := by
    have hc := causal_weighted_BCF_full_kernel_continuousOn_nonnegative
      K β w f hK
    have hLinear : Continuous (fun x : ℝ => -(w * x)) :=
      (continuous_const.mul continuous_id).neg
    have hExp : Continuous (fun x : ℝ => Real.exp (-(w * x))) :=
      Real.continuous_exp.comp hLinear
    have hSub : ContinuousOn (fun x : ℝ => 1 -
        (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
          (Real.exp (w * s) *
            f ⟨max s 0, le_max_right s 0⟩) ∂volume))
        (Ici (0 : ℝ)) := continuousOn_const.sub hc
    exact (hExp.continuousOn.mul hSub).div_const a
  let m : ℝ := ∫ t in Ioi (0 : ℝ),
    Real.exp (-w * t) * |β + K t| ∂volume
  obtain ⟨hm0, hma, hb⟩ :=
    causal_weighted_BCF_affine_pointwise_bound K a β w ha hw hK hsmall
  have hLift (f : BoundedContinuousFunction ℝ≥0 ℝ) :
      ∃ q : BoundedContinuousFunction ℝ≥0 ℝ,
        ∀ x : ℝ≥0, q x = F f (x : ℝ) := by
    apply causal_BCF_lift_of_nonnegative_uniform_bound
      (F f) ((1 + ‖f‖ * m) / a) (hC f)
    intro x hx
    exact hb f x hx
  let T : BoundedContinuousFunction ℝ≥0 ℝ →
      BoundedContinuousFunction ℝ≥0 ℝ :=
    fun f => Classical.choose (hLift f)
  refine ⟨T, ?_⟩
  intro f x hx
  exact Classical.choose_spec (hLift f) ⟨x, hx⟩
