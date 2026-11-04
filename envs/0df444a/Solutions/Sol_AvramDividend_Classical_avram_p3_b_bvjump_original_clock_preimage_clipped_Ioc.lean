-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_clock_preimage_clipped_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:43:31.606771+00:00
-- url     : https://prove2.me/submissions/b866f525-ecea-42a5-bc10-0484d04ef505

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (s t T : ℝ≥0) :
    (Real.toNNReal ⁻¹' Ioc s t) ∩ Icc (0 : ℝ) (T : ℝ) =
      (Real.toNNReal ⁻¹' Ioc s (min t T)) ∩ Icc (0 : ℝ) (T : ℝ) := by
  ext u
  simp only [mem_inter_iff, mem_preimage, mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨⟨hsu, hut⟩, hu0, huT⟩
    have hcoe : (Real.toNNReal u : ℝ) = u :=
      Real.coe_toNNReal u hu0
    have hNN : Real.toNNReal u ≤ T := by
      rw [← hcoe] at huT
      exact_mod_cast huT
    exact ⟨⟨hsu, le_min hut hNN⟩, hu0, huT⟩
  · rintro ⟨⟨hsu, hut⟩, hu0, huT⟩
    exact ⟨⟨hsu, hut.trans (min_le_left t T)⟩, hu0, huT⟩
