-- Prove2me | solution 1 for AvramDividend.Classical.causal_shift_indicator_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:52:53.253029+00:00
-- url     : https://prove2.me/submissions/7ec11c43-5518-4d32-8e38-43cd6c368ffc

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (g : ℝ → ℝ) (u x : ℝ) (hu : 0 ≤ u) (hux : u ≤ x) :
    (∫ t in Ioc (0 : ℝ) x,
      ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
    (∫ t in Ioc u x, g (t - u) ∂volume) := by
  have hmain :
      (∫ t in Ioc (0 : ℝ) x,
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
      (∫ t in Ioc (0 : ℝ) x,
        ((Ioc u x).indicator (fun z : ℝ => g (z - u))) t ∂volume) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    by_cases htu : u < t
    · have hmem : t - u ∈ Ioc (0 : ℝ) x := by
        constructor
        · exact sub_pos.mpr htu
        · linarith [ht.2, hu]
      have hmem2 : t ∈ Ioc u x := ⟨htu, ht.2⟩
      simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem2]
    · have hnot : t - u ∉ Ioc (0 : ℝ) x := by
        intro hs
        have hle : t - u ≤ 0 := sub_nonpos.mpr (le_of_not_gt htu)
        exact (not_lt_of_ge hle) hs.1
      have hnot2 : t ∉ Ioc u x := by
        intro hs
        exact htu hs.1
      simp only [Set.indicator_of_notMem hnot,
        Set.indicator_of_notMem hnot2]
  rw [hmain, setIntegral_indicator measurableSet_Ioc]
  have hsub : Ioc u x ⊆ Ioc (0 : ℝ) x := by
    intro t ht
    exact ⟨lt_of_le_of_lt hu ht.1, ht.2⟩
  rw [Set.inter_eq_right.mpr hsub]
