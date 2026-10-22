-- Prove2me | solution 1 for AvramDividend.Classical.lipschitz_payoff_integrable_of_integrable_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:02:18.349497+00:00
-- url     : https://prove2.me/submissions/b0817b19-e9e8-4899-814a-eaf16f6e5854

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_lipschitz_shifted_payoff_integrable_of_L1_difference

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℝ → ℝ) (hf : Measurable f) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z Y : Ω → ℝ) (hZ : Measurable Z) (hY : Measurable Y)
    (hZI : Integrable Z P) (hYI : Integrable Y P) :
    Integrable (fun ω => f (Z ω + Y ω)) P := by
  have hSumI : Integrable (fun ω => Z ω + Y ω) P :=
    hZI.add hYI
  have hDom :
      Integrable (fun ω => L * |(Z ω + Y ω) - 0|) P := by
    simpa only [sub_zero] using hSumI.abs.const_mul L
  have hBase :
      Integrable (fun _ : Ω => f ((0 : ℝ) + 0)) P := by
    simpa only [zero_add] using
      (integrable_const (f 0) : Integrable (fun _ : Ω => f 0) P)
  have hRes := lipschitz_shifted_payoff_integrable_of_L1_difference
    P f hf L hLip
    (fun ω => Z ω + Y ω) (fun _ : Ω => 0) (fun _ : Ω => 0)
    (hZ.add hY) measurable_const measurable_const hBase hDom
  simpa only [add_zero] using hRes
