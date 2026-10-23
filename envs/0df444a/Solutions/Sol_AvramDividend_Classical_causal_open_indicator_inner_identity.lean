-- Prove2me | solution 1 for AvramDividend.Classical.causal_open_indicator_inner_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:58:11.323557+00:00
-- url     : https://prove2.me/submissions/0e567118-b522-490a-9647-fb9685c4ea3c

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- A causal finite interval convolution equals its open-indicator whole-line form. -/
theorem solution
    (K g : ℝ → ℝ) (t x : ℝ)
    (ht : 0 ≤ t) (htx : t ≤ x) :
    (∫ u in Ioc (0 : ℝ) t, K u * g (t - u) ∂volume) =
    (∫ u : ℝ,
      ((Ioi (0 : ℝ)).indicator K) u *
      ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) := by
  calc
    (∫ u in Ioc (0 : ℝ) t, K u * g (t - u) ∂volume) =
      ∫ u in Ioo (0 : ℝ) t, K u * g (t - u) ∂volume :=
        integral_Ioc_eq_integral_Ioo
    _ = ∫ u : ℝ,
        (Ioo (0 : ℝ) t).indicator (fun v => K v * g (t - v)) u ∂volume :=
          (integral_indicator measurableSet_Ioo).symm
    _ = ∫ u : ℝ,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume := by
          congr 1
          funext u
          by_cases hu : u ∈ Ioo (0 : ℝ) t
          · have hpos : u ∈ Ioi (0 : ℝ) := hu.1
            have hshift : t - u ∈ Ioc (0 : ℝ) x := by
              constructor
              · linarith [hu.2]
              · linarith [hu.1, htx]
            simp only [Set.indicator_of_mem hu,
              Set.indicator_of_mem hpos, Set.indicator_of_mem hshift]
          · by_cases hup : u ∈ Ioi (0 : ℝ)
            · have hshift : t - u ∉ Ioc (0 : ℝ) x := by
                intro h
                have hut : u < t := by linarith [h.1]
                exact hu ⟨hup, hut⟩
              simp only [Set.indicator_of_notMem hu,
                Set.indicator_of_mem hup, Set.indicator_of_notMem hshift,
                mul_zero]
            · simp only [Set.indicator_of_notMem hu,
                Set.indicator_of_notMem hup, zero_mul]
