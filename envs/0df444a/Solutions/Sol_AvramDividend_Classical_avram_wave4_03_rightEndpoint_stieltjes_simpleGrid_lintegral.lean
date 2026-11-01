-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_rightEndpoint_stieltjes_simpleGrid_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:25:01.150209+00:00
-- url     : https://prove2.me/submissions/b5e0e446-36f1-4761-93c7-577cfebba117

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (g : ℝ → ℝ) (hg : Monotone g)
    (u : ℕ → ℝ) (n : ℕ) (c : ℕ → ℝ≥0∞) :
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i) (u (i + 1))).indicator
        (fun _ : ℝ => c (i + 1)) t
      ∂hg.stieltjesFunction.measure) =
    ∑ i ∈ Finset.range n,
      c (i + 1) *
        ENNReal.ofReal
          (hg.stieltjesFunction (u (i + 1)) -
            hg.stieltjesFunction (u i)) := by
  classical
  calc
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i) (u (i + 1))).indicator
        (fun _ : ℝ => c (i + 1)) t
      ∂hg.stieltjesFunction.measure) =
      ∑ i ∈ Finset.range n,
        (∫⁻ t : ℝ,
          (Ioc (u i) (u (i + 1))).indicator
            (fun _ : ℝ => c (i + 1)) t
          ∂hg.stieltjesFunction.measure) := by
        exact lintegral_finset_sum (Finset.range n) (by
          intro i hi
          exact measurable_const.indicator measurableSet_Ioc)
    _ = ∑ i ∈ Finset.range n,
      c (i + 1) * hg.stieltjesFunction.measure (Ioc (u i) (u (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact lintegral_indicator_const measurableSet_Ioc (c (i + 1))
    _ = ∑ i ∈ Finset.range n,
      c (i + 1) *
        ENNReal.ofReal (hg.stieltjesFunction (u (i + 1)) -
          hg.stieltjesFunction (u i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [StieltjesFunction.measure_Ioc]
