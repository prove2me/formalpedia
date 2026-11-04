-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_clock_after_horizon_preimage_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:34:30.324618+00:00
-- url     : https://prove2.me/submissions/5c51eec8-ae75-483d-87a9-34c42ac9e82b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (s t T : ℝ≥0) (hTs : T ≤ s) :
    (Real.toNNReal ⁻¹' Ioc s t) ∩ Icc (0 : ℝ) (T : ℝ) = ∅ := by
  ext u
  simp only [mem_inter_iff, mem_preimage, mem_Ioc, mem_Icc,
    mem_empty_iff_false, iff_false]
  rintro ⟨⟨hsu, _⟩, hu0, huT⟩
  have hcoe : (Real.toNNReal u : ℝ) = u :=
    Real.coe_toNNReal u hu0
  have hsuR : (s : ℝ) < u := by
    rw [← hcoe]
    exact_mod_cast hsu
  have hTsR : (T : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hTs
  exact (not_lt_of_ge (huT.trans hTsR)) hsuR
