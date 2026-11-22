-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_positive_time_pushforward_clock_mass_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:23:15.651786+00:00
-- url     : https://prove2.me/submissions/2e6ee905-faf2-4be7-973e-d615f43e4d0f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (T : ℝ≥0) :
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc (0 : ℝ≥0) T) = (T : ℝ≥0∞) := by
  classical
  have hpre :
      Real.toNNReal ⁻¹' Ioc (0 : ℝ≥0) T ∩ Icc (0 : ℝ) (T : ℝ) =
        Ioc (0 : ℝ) (T : ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Ioc, Set.mem_Icc]
    constructor
    · rintro ⟨⟨hnn0, _⟩, ⟨hx0, hxT⟩⟩
      have hxpos : 0 < x := by
        have hcoe : (0 : ℝ) < (Real.toNNReal x : ℝ) := by
          exact_mod_cast hnn0
        simpa [Real.coe_toNNReal x hx0] using hcoe
      exact ⟨hxpos, hxT⟩
    · rintro ⟨hxpos, hxT⟩
      have hx0 : 0 ≤ x := le_of_lt hxpos
      have hpos : (0 : ℝ≥0) < Real.toNNReal x := by
        have hcoe : (0 : ℝ) < (Real.toNNReal x : ℝ) := by
          simpa [Real.coe_toNNReal x hx0] using hxpos
        exact_mod_cast hcoe
      have hle : Real.toNNReal x ≤ T := by
        have hcoe : (Real.toNNReal x : ℝ) ≤ (T : ℝ) := by
          simpa [Real.coe_toNNReal x hx0] using hxT
        exact_mod_cast hcoe
      exact ⟨⟨hpos, hle⟩, ⟨hx0, hxT⟩⟩
  rw [Measure.map_apply measurable_real_toNNReal measurableSet_Ioc]
  rw [Measure.restrict_apply
    (measurable_real_toNNReal measurableSet_Ioc)]
  rw [hpre, Real.volume_Ioc]
  simp
