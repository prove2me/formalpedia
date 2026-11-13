-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a51_stopped_raw_tail_energy_lintegral_le_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:16:46.660043+00:00
-- url     : https://prove2.me/submissions/974799d3-393e-4e07-94b5-4db6bd635b43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a50_small_drift_large_raw_increment_energy_le_centered
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped physical mesh raw large-tail energy is dominated by its centred source tail. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ) (s : ℕ → ℝ≥0)
    (ρ : Ω → ℝ≥0) (Z : ℕ → Ω → ℝ)
    (d η : ℝ) (hη : 0 < η) (hd : |d| ≤ η / 2)
    (hMeas : Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s i < ρ ω then
        ENNReal.ofReal (if η / 2 ≤ |Z i ω| then (Z i ω)^2 else 0)
      else 0)) :
    (∫⁻ ω, ∑ i ∈ Finset.range m,
      if s i < ρ ω then
        ENNReal.ofReal
          (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0)
      else 0 ∂P) ≤
    (4 : ℝ≥0∞) * (∫⁻ ω, ∑ i ∈ Finset.range m,
      if s i < ρ ω then
        ENNReal.ofReal (if η / 2 ≤ |Z i ω| then (Z i ω)^2 else 0)
      else 0 ∂P) := by
  classical
  have hTerm (i : ℕ) (ω : Ω) :
      ENNReal.ofReal
        (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0) ≤
      (4 : ℝ≥0∞) *
        ENNReal.ofReal (if η / 2 ≤ |Z i ω| then (Z i ω)^2 else 0) := by
    calc
      ENNReal.ofReal
        (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0) ≤
        ENNReal.ofReal
          (4 * (if η / 2 ≤ |Z i ω| then (Z i ω)^2 else 0)) :=
        ENNReal.ofReal_le_ofReal
          (avram_ga_a50_small_drift_large_raw_increment_energy_le_centered
            (Z i ω) d η hη hd)
      _ = (4 : ℝ≥0∞) *
          ENNReal.ofReal (if η / 2 ≤ |Z i ω| then
            (Z i ω)^2 else 0) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  have hPoint (ω : Ω) :
      (∑ i ∈ Finset.range m, if s i < ρ ω then
        ENNReal.ofReal
          (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0)
      else 0) ≤
      (4 : ℝ≥0∞) * (∑ i ∈ Finset.range m,
        if s i < ρ ω then
          ENNReal.ofReal
            (if η / 2 ≤ |Z i ω| then (Z i ω)^2 else 0)
        else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : s i < ρ ω
    · simpa only [if_pos h] using hTerm i ω
    · simp only [if_neg h, mul_zero, le_refl]
  calc
    (∫⁻ ω, ∑ i ∈ Finset.range m,
      if s i < ρ ω then
        ENNReal.ofReal
          (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0)
      else 0 ∂P) ≤
      (∫⁻ ω, (4 : ℝ≥0∞) * (∑ i ∈ Finset.range m,
        if s i < ρ ω then ENNReal.ofReal
          (if η / 2 ≤ |Z i ω| then (Z i ω)^2 else 0)
        else 0) ∂P) :=
      lintegral_mono hPoint
    _ = (4 : ℝ≥0∞) * (∫⁻ ω, ∑ i ∈ Finset.range m,
        if s i < ρ ω then ENNReal.ofReal
          (if η / 2 ≤ |Z i ω| then (Z i ω)^2 else 0)
        else 0 ∂P) :=
      lintegral_const_mul _ hMeas
