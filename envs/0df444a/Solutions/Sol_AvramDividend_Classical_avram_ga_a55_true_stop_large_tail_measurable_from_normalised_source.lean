-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a55_true_stop_large_tail_measurable_from_normalised_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:28:45.074209+00:00
-- url     : https://prove2.me/submissions/6392bd6e-4012-420e-8ea4-139942f646bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a54_true_stop_mask_large_source_tail_sum_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Normalised original Gaussian increment measurability gives stopped raw-source tail measurability. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (S : Finset ℕ) (s : ℕ → ℝ≥0)
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (Z : ℕ → Ω → ℝ) (σ : ℝ) (hσ : σ ≠ 0)
    (hNormMeas : ∀ i ∈ S,
      Measurable (fun ω : Ω => Z i ω / σ))
    (η : ℝ) :
    Measurable (fun ω : Ω =>
      Finset.sum S (fun i =>
        if s i < ρ ω then
          ENNReal.ofReal (if η ≤ |Z i ω| then (Z i ω)^2 else 0)
        else 0)) := by
  have hZ (i : ℕ) (hi : i ∈ S) : Measurable (Z i) := by
    have hm : Measurable (fun ω : Ω => (Z i ω / σ) * σ) :=
      (hNormMeas i hi).mul_const σ
    have heq : (fun ω : Ω => (Z i ω / σ) * σ) = Z i := by
      funext ω
      field_simp [hσ]
    simpa only [heq] using hm
  exact avram_ga_a54_true_stop_mask_large_source_tail_sum_measurable
    S s ρ hρ Z hZ η
