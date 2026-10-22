-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_of_ordered_integrated_excursion_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T23:37:50.447168+00:00
-- url     : https://prove2.me/submissions/71020694-03df-4abf-88d7-945a3ab37e0c

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_positive_integrated_excursion_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem solution (T W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hT : ContinuousOn T (Ioi (0 : ℝ)))
    (hordered : ∀ u v : ℝ, 0 < u → u ≤ v →
      W v = W u * Real.exp (∫ t in u..v, T t)) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  have hanchor : ∀ x : ℝ, 0 < x →
      W x = W a * Real.exp (∫ t in a..x, T t) := by
    intro x hx
    rcases le_total a x with hax | hxa
    · exact hordered a x ha hax
    · have heq := hordered x a hx hxa
      have hsymm : (∫ t in a..x, T t) =
          -(∫ t in x..a, T t) := by
        rw [intervalIntegral.integral_symm]
      rw [hsymm, Real.exp_neg, heq]
      simp
  exact contDiffOn_one_of_positive_integrated_excursion_tail
    T W a (W a) ha hT hanchor
