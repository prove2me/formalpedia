-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_two_input_lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:01:08.073797+00:00
-- url     : https://prove2.me/submissions/a654afd2-9e6c-420a-8e67-042680f73953

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_explicit_kernel_mass_bound
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_locally_bounded_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_local_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The weighted Volterra operator has a fixed Lipschitz coefficient. -/
theorem solution
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    let m := ∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume
    0 ≤ m ∧ m < a ∧
      ∀ (f h : BoundedContinuousFunction ℝ≥0 ℝ)
        (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R),
        Real.exp (-(w * x)) *
          |(∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
              (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume) -
           (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
              (Real.exp (w * s) * h ⟨max s 0, le_max_right s 0⟩) ∂volume)| ≤
          ‖f - h‖ * m := by
  dsimp
  obtain ⟨hm0, hma, hbound⟩ :=
    causal_weighted_BCF_explicit_kernel_mass_bound K a β w ha hw hK hsmall
  refine ⟨hm0, hma, ?_⟩
  intro f h R x hR hx
  let V : BoundedContinuousFunction ℝ≥0 ℝ → ℝ → ℝ :=
    fun z s => Real.exp (w * s) * z ⟨max s 0, le_max_right s 0⟩
  have hVc (z : BoundedContinuousFunction ℝ≥0 ℝ) :
      ContinuousOn (V z) (Ioi (0 : ℝ)) :=
    (causal_weighted_BCF_extension_continuous z w).continuousOn
  have hVb (z : BoundedContinuousFunction ℝ≥0 ℝ) :
      ∀ r : ℝ, 0 < r →
        ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) r → |V z s| ≤ C := by
    intro r hr
    exact causal_weighted_BCF_local_bound z w r hr
  have hi (z : BoundedContinuousFunction ℝ≥0 ℝ) :
      IntegrableOn (fun s : ℝ => (β + K (x - s)) * V z s)
        (Ioc (0 : ℝ) x) volume :=
    causal_full_kernel_locally_bounded_input_integrable
      K (V z) β hK (hVc z) (hVb z) x hx.1
  have hIntegralSub :
      (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V f s ∂volume) -
      (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V h s ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V (f - h) s ∂volume) := by
    rw [← integral_sub (hi f) (hi h)]
    apply integral_congr_ae
    filter_upwards [] with s
    change
      (β + K (x - s)) *
          (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) -
        (β + K (x - s)) *
          (Real.exp (w * s) * h ⟨max s 0, le_max_right s 0⟩) =
        (β + K (x - s)) *
          (Real.exp (w * s) *
            (f ⟨max s 0, le_max_right s 0⟩ -
             h ⟨max s 0, le_max_right s 0⟩))
    ring
  calc
    Real.exp (-(w * x)) *
        |(∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V f s ∂volume) -
         (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V h s ∂volume)| =
      Real.exp (-(w * x)) *
        |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V (f - h) s ∂volume| := by
          rw [hIntegralSub]
    _ ≤ ‖f - h‖ *
        (∫ t in Ioi (0 : ℝ), Real.exp (-w * t) * |β + K t| ∂volume) :=
      hbound (f - h) R x hR hx
