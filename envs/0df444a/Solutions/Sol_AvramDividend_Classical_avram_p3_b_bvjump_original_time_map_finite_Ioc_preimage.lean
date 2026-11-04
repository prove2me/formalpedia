-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:19:33.09088+00:00
-- url     : https://prove2.me/submissions/35dfa40e-f7d1-4e24-a416-f7085b6ca673

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (s t T : ℝ≥0) (htT : t ≤ T) :
    (Real.toNNReal ⁻¹' Ioc s t) ∩ Icc (0 : ℝ) (T : ℝ) =
      Ioc (s : ℝ) (t : ℝ) := by
  ext u
  simp only [mem_inter_iff, mem_preimage, mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨⟨hsu, hut⟩, hu0, huT⟩
    have hcoe : (Real.toNNReal u : ℝ) = u :=
      Real.coe_toNNReal u hu0
    rw [← hcoe]
    constructor
    · exact_mod_cast hsu
    · exact_mod_cast hut
  · rintro ⟨hsu, hut⟩
    have hu0 : (0 : ℝ) ≤ u :=
      le_trans (NNReal.coe_nonneg s) (le_of_lt hsu)
    have huT : u ≤ (T : ℝ) :=
      le_trans hut (by exact_mod_cast htT)
    refine ⟨⟨?_, ?_⟩, hu0, huT⟩
    · apply NNReal.coe_lt_coe.mp
      simpa only [Real.coe_toNNReal u hu0] using hsu
    · apply NNReal.coe_le_coe.mp
      simpa only [Real.coe_toNNReal u hu0] using hut
