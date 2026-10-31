-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_tent_positive_tail_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:50:33.901448+00:00
-- url     : https://prove2.me/submissions/6532705e-d63c-4cd9-a4e4-2318689a89b7

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral

/-- The weighted second-derivative tent has no more positive-tail mass
    than its exact quadratic kernel mass times the source L1 norm. -/
theorem solution
    (r : ℝ) (hr : 0 ≤ r) (H : ℝ → ℝ)
    (hH : Integrable H volume) (hH0 : ∀ x : ℝ, 0 ≤ H x) :
    (∫ x in Ioi r,
      MeasureTheory.convolution
        ((Ioc (0 : ℝ) r).indicator (fun t => r - t)) H
        (ContinuousLinearMap.mul ℝ ℝ) volume x) ≤
      (r ^ 2 / 2) * (∫ x : ℝ, H x) := by
  let K : ℝ → ℝ := (Ioc (0 : ℝ) r).indicator (fun t => r - t)
  have hK : Integrable K volume := by
    dsimp [K]
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mp
      ((continuous_const.sub continuous_id).intervalIntegrable _ _)
  have hK0 : ∀ t : ℝ, 0 ≤ K t := by
    intro t
    dsimp [K]
    by_cases ht : t ∈ Ioc (0 : ℝ) r
    · simp only [Set.indicator_of_mem ht]
      exact sub_nonneg.mpr ht.2
    · simp [Set.indicator, ht]
  have hconv : Integrable
      (MeasureTheory.convolution K H (ContinuousLinearMap.mul ℝ ℝ) volume)
      volume :=
    MeasureTheory.Integrable.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ) hK hH
  have hconv0 : ∀ x : ℝ,
      0 ≤ MeasureTheory.convolution K H
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
    intro x
    change 0 ≤ ∫ t : ℝ, K t * H (x - t)
    exact integral_nonneg (fun t => mul_nonneg (hK0 t) (hH0 (x - t)))
  have hmass : (∫ t : ℝ, K t) = r ^ 2 / 2 := by
    dsimp [K]
    have hc : (∫ t in (0 : ℝ)..r, r - t) = r ^ 2 / 2 := by
      calc
        _ = (∫ t in (0 : ℝ)..r, r) - (∫ t in (0 : ℝ)..r, t) := by
          simpa only [id_eq] using (intervalIntegral.integral_sub
            (f := fun _ : ℝ => r) (g := id) intervalIntegrable_const
            (continuous_id.intervalIntegrable _ _))
        _ = r ^ 2 / 2 := by
          rw [intervalIntegral.integral_const, integral_id]
          ring
    rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [← intervalIntegral.integral_of_le hr]
    exact hc
  have hfactor := MeasureTheory.integral_convolution
    (L := ContinuousLinearMap.mul ℝ ℝ) hK hH
  rw [hmass] at hfactor
  calc
    (∫ x in Ioi r, MeasureTheory.convolution K H
      (ContinuousLinearMap.mul ℝ ℝ) volume x) ≤
      ∫ x : ℝ, MeasureTheory.convolution K H
        (ContinuousLinearMap.mul ℝ ℝ) volume x :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall hconv0) hconv
    _ = (r ^ 2 / 2) * (∫ x : ℝ, H x) := by
      convert hfactor using 1
      rfl
