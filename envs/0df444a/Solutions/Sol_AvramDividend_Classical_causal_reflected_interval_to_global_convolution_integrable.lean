-- Prove2me | solution 1 for AvramDividend.Classical.causal_reflected_interval_to_global_convolution_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:11:44.239692+00:00
-- url     : https://prove2.me/submissions/a5b34db1-f6f8-4467-8e02-6c96576ffae0

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Causal support promotes an interval-integrable reflected product to full convolution integrability. -/
theorem solution
    (k F : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hkzero : ∀ t : ℝ, t ≤ 0 → k t = 0)
    (hFzero : ∀ t : ℝ, t ≤ 0 → F t = 0)
    (hi : IntervalIntegrable
      (fun s : ℝ => k (x - s) * F s) volume 0 x) :
    Integrable (fun y : ℝ => k y * F (x - y)) volume := by
  let h : ℝ → ℝ := fun s => k (x - s) * F s
  have hIoc : IntegrableOn h (Ioc (0 : ℝ) x) volume := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hi
  have hout (s : ℝ) (hs : s ∉ Ioc (0 : ℝ) x) : h s = 0 := by
    by_cases hs0 : s ≤ 0
    · simp [h, hFzero s hs0]
    · have hspos : 0 < s := lt_of_not_ge hs0
      have hxs : x ≤ s := by
        by_contra hn
        have hsx : s ≤ x := le_of_not_ge hn
        exact hs ⟨hspos, hsx⟩
      have hks : k (x - s) = 0 :=
        hkzero (x - s) (sub_nonpos.mpr hxs)
      simp [h, hks]
  have hind : (Ioc (0 : ℝ) x).indicator h = h := by
    funext s
    by_cases hs : s ∈ Ioc (0 : ℝ) x
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs, hout s hs]
  have hglobal : Integrable h volume := by
    rw [← hind]
    exact hIoc.integrable_indicator measurableSet_Ioc
  have hneg : Measure.map (fun y : ℝ => -y) volume = volume := by
    simpa [neg_one_mul] using
      (Real.map_volume_mul_left (a := (-1 : ℝ)) (neg_ne_zero.mpr one_ne_zero))
  letI : (volume : Measure ℝ).IsNegInvariant := ⟨by
    change Measure.map (fun y : ℝ => -y) volume = volume
    exact hneg⟩
  have hreflected : Integrable (fun y : ℝ => h (x - y)) volume :=
    hglobal.comp_sub_left x
  have heq : (fun y : ℝ => h (x - y)) =
      (fun y : ℝ => k y * F (x - y)) := by
    funext y
    dsimp [h]
    congr 1
    ring
  rwa [heq] at hreflected
