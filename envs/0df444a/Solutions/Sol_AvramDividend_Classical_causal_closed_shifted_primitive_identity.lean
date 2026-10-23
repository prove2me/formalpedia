-- Prove2me | solution 1 for AvramDividend.Classical.causal_closed_shifted_primitive_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:01:29.79955+00:00
-- url     : https://prove2.me/submissions/1c96f280-ef61-4a8d-bda4-f28bca38fc33

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_shift_window_change_of_variables

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (g : ℝ → ℝ) (u x : ℝ)
    (hu : 0 < u) (hux : u ≤ x) :
    (∫ t in Ioc (0 : ℝ) x,
      ((Icc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
    (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) := by
  have hlocal :
      (∫ t in Ioc (0 : ℝ) x,
        ((Icc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
      (∫ t in Ioc (0 : ℝ) x,
        ((Icc u x).indicator (fun z : ℝ => g (z - u))) t ∂volume) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    by_cases htu : u ≤ t
    · have hsub : t - u ∈ Icc (0 : ℝ) x := by
        constructor
        · exact sub_nonneg.mpr htu
        · linarith [ht.2, hu]
      have hmem : t ∈ Icc u x := ⟨htu, ht.2⟩
      simp only [Set.indicator_of_mem hsub, Set.indicator_of_mem hmem]
    · have hnot : t - u ∉ Icc (0 : ℝ) x := by
        intro hs
        exact htu (sub_nonneg.mp hs.1)
      have hnot2 : t ∉ Icc u x := by
        intro hs
        exact htu hs.1
      simp only [Set.indicator_of_notMem hnot,
        Set.indicator_of_notMem hnot2]
  calc
    _ = ∫ t in Ioc (0 : ℝ) x,
          ((Icc u x).indicator (fun z : ℝ => g (z - u))) t ∂volume :=
      hlocal
    _ = ∫ t in Icc u x, g (t - u) ∂volume := by
      rw [setIntegral_indicator measurableSet_Icc]
      have hsub : Icc u x ⊆ Ioc (0 : ℝ) x := by
        intro t ht
        exact ⟨lt_of_lt_of_le hu ht.1, ht.2⟩
      rw [Set.inter_eq_right.mpr hsub]
    _ = ∫ t in Ioc u x, g (t - u) ∂volume :=
      integral_Icc_eq_integral_Ioc
    _ = ∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume :=
      causal_shift_window_change_of_variables g u x hux
