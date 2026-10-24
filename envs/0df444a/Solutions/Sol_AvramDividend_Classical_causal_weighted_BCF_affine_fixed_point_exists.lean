-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_affine_fixed_point_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:25:34.602263+00:00
-- url     : https://prove2.me/submissions/5e5ad998-57c9-4cfd-b01d-6db1502f0d92

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_affine_selfmap_exists
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_affine_pointwise_lipschitz
import Theorems.Thm_AvramDividend_Classical_causal_BCF_contraction_of_pointwise_bound
import Theorems.Thm_AvramDividend_Classical_causal_bounded_continuous_contraction_fixed_point
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_fixed_point_equation_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A strict causal weighted Volterra affine map has a fixed point. -/
theorem solution
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    ∃ f : BoundedContinuousFunction ℝ≥0 ℝ,
      ∀ x : ℝ, 0 < x →
        a * (Real.exp (w * x) * f ⟨max x 0, le_max_right x 0⟩) +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) *
              (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩)
              ∂volume) = 1 := by
  let m : ℝ := ∫ t in Ioi (0 : ℝ),
    Real.exp (-w * t) * |β + K t| ∂volume
  obtain ⟨T, hT⟩ :=
    causal_weighted_BCF_affine_selfmap_exists K a β w ha hw hK hsmall
  obtain ⟨hm0, hma, hPoint⟩ :=
    causal_weighted_BCF_affine_pointwise_lipschitz K a β w ha hw hK hsmall
  have hMetric : ∀ (f h : BoundedContinuousFunction ℝ≥0 ℝ)
      (x : ℝ≥0), dist (T f x) (T h x) ≤ (m / a) * dist f h := by
    intro f h x
    rcases x with ⟨x, hx⟩
    have hb := hPoint f h x hx
    rw [← hT f x hx, ← hT h x hx] at hb
    calc
      dist (T f ⟨x, hx⟩) (T h ⟨x, hx⟩) =
          |T f ⟨x, hx⟩ - T h ⟨x, hx⟩| := Real.dist_eq _ _
      _ ≤ ‖f - h‖ * (m / a) := hb
      _ = (m / a) * dist f h := by rw [dist_eq_norm]; ring
  obtain ⟨c, hc, hLip⟩ :=
    causal_BCF_contraction_of_pointwise_bound T a m ha hm0 hma hMetric
  obtain ⟨f, hFixed⟩ :=
    causal_bounded_continuous_contraction_fixed_point T c hc hLip
  exact ⟨f, causal_weighted_BCF_fixed_point_equation_transfer
    K a β w ha T f hT hFixed⟩
