-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva91_original_mapped_levy_compensator_time_zero_atom_null_any_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:53:34.095197+00:00
-- url     : https://prove2.me/submissions/2ff9abc8-bde8-453f-ba06-7bfbabdbe189

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (S : ℝ≥0) :
    (((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal)
      ({0} : Set ℝ≥0) = 0 := by
  have hMeas : Measurable Real.toNNReal := measurable_real_toNNReal
  have hSet : MeasurableSet ({0} : Set ℝ≥0) := measurableSet_singleton 0
  rw [Measure.map_apply hMeas hSet]
  have hPre : MeasurableSet (Real.toNNReal ⁻¹' ({0} : Set ℝ≥0)) :=
    hMeas hSet
  rw [Measure.restrict_apply hPre]
  have hInter :
      (Real.toNNReal ⁻¹' ({0} : Set ℝ≥0)) ∩ Icc 0 (S : ℝ) =
      ({0} : Set ℝ) := by
    ext t
    constructor
    · intro ht
      rcases ht with ⟨ht0, htI⟩
      have hle : t ≤ 0 := Real.toNNReal_eq_zero.mp ht0
      exact le_antisymm hle htI.1
    · intro ht
      have ht0 : t = 0 := ht
      subst t
      simp
  rw [hInter]
  simp
