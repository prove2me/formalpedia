-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB129_bounded_measurable_squared_difference_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:51:14.672065+00:00
-- url     : https://prove2.me/submissions/5ed84f10-ec4d-494b-a509-269be2565909

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section


theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ ω, |f ω| ≤ B) (hgb : ∀ ω, |g ω| ≤ B) :
    Integrable (fun ω => (f ω - g ω) ^ 2) P := by
  have hm : Measurable (fun ω => (f ω - g ω) ^ 2) := (hf.sub hg).pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable (4 * B ^ 2)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_pow]
  have ha : |f ω - g ω| ≤ 2 * B := by
    calc
      |f ω - g ω| ≤ |f ω| + |g ω| := by
        simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (f ω) 0 (g ω))
      _ ≤ B + B := add_le_add (hfb ω) (hgb ω)
      _ = 2 * B := by ring
  calc
    |f ω - g ω| ^ 2 ≤ (2 * B) ^ 2 := by gcongr
    _ = 4 * B ^ 2 := by ring
