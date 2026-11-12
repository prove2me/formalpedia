-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB97_bounded_step_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:04:18.471326+00:00
-- url     : https://prove2.me/submissions/c2686b55-ef09-42bb-9a03-2d6b9356ba53

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (G : ℕ → ℕ → Ω → ℝ)
    (hG : ∀ a i, StronglyMeasurable (G a i))
    (B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ a i ω, |G a i ω| ≤ B)
    (m p r : ℕ) :
    Integrable (fun ω => (G m (r / (p + 1)) ω -
      G p (r / (m + 1)) ω) ^ 2) P := by
  have hsm : StronglyMeasurable
      (fun ω => (G m (r / (p + 1)) ω -
        G p (r / (m + 1)) ω) ^ 2) :=
    ((hG m (r / (p + 1))).sub (hG p (r / (m + 1)))).pow 2
  apply Integrable.of_bound hsm.aestronglyMeasurable ((2 * B) ^ 2)
  filter_upwards [] with ω
  have ha := hBound m (r / (p + 1)) ω
  have hb := hBound p (r / (m + 1)) ω
  have hdiff :
      |G m (r / (p + 1)) ω - G p (r / (m + 1)) ω| ≤
      2 * B := by
    calc
      _ ≤ |G m (r / (p + 1)) ω| +
          |G p (r / (m + 1)) ω| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (G m (r / (p + 1)) ω) 0
            (G p (r / (m + 1)) ω))
      _ ≤ B + B := add_le_add ha hb
      _ = 2 * B := by ring
  simp only [Real.norm_eq_abs, abs_pow]
  have hupper : 0 ≤ 2 * B := by positivity
  have hnonneg := mul_nonneg (sub_nonneg.mpr hdiff)
    (add_nonneg hupper (abs_nonneg
      (G m (r / (p + 1)) ω - G p (r / (m + 1)) ω)))
  nlinarith [hnonneg]
