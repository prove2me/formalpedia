-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_finite_cap_floor_positive_interior_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T11:00:50.602731+00:00
-- url     : https://prove2.me/submissions/8a829b18-f77b-4f57-b1bb-f4d385e9b196

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal ENNReal Topology
theorem solution (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤) :
    (∀ n : ℕ, 0 < C.toReal / ((n : ℝ) + 2) ∧
      ENNReal.ofReal (C.toReal / ((n : ℝ) + 2)) < C) ∧
    Tendsto (fun n : ℕ => C.toReal / ((n : ℝ) + 2))
      atTop (𝓝 (0 : ℝ)) := by
  have hCReal : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFinite
  constructor
  · intro n
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hnum : 0 < C.toReal / ((n : ℝ) + 2) :=
      div_pos hCReal hden
    refine ⟨hnum, (ENNReal.ofReal_lt_iff_lt_toReal
      hnum.le hFinite).2 ?_⟩
    apply (div_lt_iff₀ hden).2
    nlinarith
  · have hShift :=
      (tendsto_const_div_atTop_nhds_zero_nat C.toReal).comp
        (Filter.tendsto_add_atTop_nat 2)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat]
      using hShift
