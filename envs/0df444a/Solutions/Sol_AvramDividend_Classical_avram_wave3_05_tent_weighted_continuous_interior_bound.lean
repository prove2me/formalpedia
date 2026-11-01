-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_tent_weighted_continuous_interior_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:20:47.407988+00:00
-- url     : https://prove2.me/submissions/cb7c48e4-9a80-41b2-9884-d31dc5dffd39

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_local_interval_integrability
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_pointwise_convolution
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_weighted_interval_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_positive_tail_mass_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

/-- Continuous positive-state curvature supplies interval integrability;
    the weighted Taylor remainder obeys the sharp quadratic L1 bound. -/
theorem solution
    (F : ℝ → ℝ) (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ)
    (hFc : ContinuousOn F (Ioi (0 : ℝ)))
    (hF : Integrable
      (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume)
    (hR : IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) *
        |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)|)
      (Ioi r) volume) :
    (∫ x in Ioi r,
      Real.exp (-θ * x) *
        |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)|) ≤
      (r ^ 2 / 2) *
        (∫ u : ℝ, Real.exp (-θ * u) * |F u|) := by
  let H : ℝ → ℝ := fun u => Real.exp (-θ * u) * |F u|
  let K : ℝ → ℝ := (Ioc (0 : ℝ) r).indicator (fun s => r - s)
  let R : ℝ → ℝ := fun x => Real.exp (-θ * x) *
    |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)|
  have hH0 : ∀ u : ℝ, 0 ≤ H u := by
    intro u
    exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hK : Integrable K volume := by
    dsimp [K]
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mp
      ((continuous_const.sub continuous_id).intervalIntegrable _ _)
  have hconv : Integrable
      (MeasureTheory.convolution K H (ContinuousLinearMap.mul ℝ ℝ) volume)
      volume :=
    MeasureTheory.Integrable.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ) hK hF
  have hpoint (x : ℝ) (hx : x ∈ Ioi r) :
      R x ≤ MeasureTheory.convolution K H
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
    have hseg := avram_wave3_05_tent_local_interval_integrability
      F hFc r x θ hr hx
    have hd := avram_wave3_05_tent_weighted_interval_domination
      F x r θ hr hθ hseg.1 hseg.2
    have heq := avram_wave3_05_tent_pointwise_convolution H x r hr
    calc
      R x ≤ ∫ s in (0 : ℝ)..r,
          (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)| := hd
      _ = ∫ s in (0 : ℝ)..r, (r - s) * H (x - s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        simp only [H]
        ring
      _ = MeasureTheory.convolution K H
            (ContinuousLinearMap.mul ℝ ℝ) volume x := heq.symm
  have hmono :
      (∫ x in Ioi r, R x) ≤
        ∫ x in Ioi r,
          MeasureTheory.convolution K H
            (ContinuousLinearMap.mul ℝ ℝ) volume x := by
    apply integral_mono_ae hR hconv.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpoint x hx
  exact hmono.trans (avram_wave3_05_tent_positive_tail_mass_bound r hr H hF hH0)
