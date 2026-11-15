-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a378_topcap_C2_positive_derivatives_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:08:38.467938+00:00
-- url     : https://prove2.me/submissions/0d6414f3-52c3-464d-98eb-81c0c5e5ac88

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology
open scoped ENNReal
noncomputable section
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ContinuousOn (deriv w) (Ioi (0 : ℝ)) ∧
      ContinuousOn (iteratedDeriv 2 w) (Ioi (0 : ℝ)) := by
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hu : UniqueDiffOn ℝ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hopen.uniqueDiffOn
  have hSub : Ioi (0 : ℝ) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    exact ⟨hy, by simp [hTopCap]⟩
  constructor
  · have hc := hw_smooth.continuousOn_iteratedDerivWithin
      (by norm_num : (1 : WithTop ENat) ≤ (2 : WithTop ENat)) hu
    have heq := iteratedDerivWithin_of_isOpen hopen (n := 1) (f := w)
    simpa only [iteratedDeriv_one] using (hc.congr heq.symm).mono hSub
  · have hc := hw_smooth.continuousOn_iteratedDerivWithin
      (by norm_num : (2 : WithTop ENat) ≤ (2 : WithTop ENat)) hu
    exact (hc.congr (iteratedDerivWithin_of_isOpen hopen
      (n := 2) (f := w)).symm).mono hSub
