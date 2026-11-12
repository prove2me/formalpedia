-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_original_ubv_actual_grid_HJB_drift_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:36:52.516771+00:00
-- url     : https://prove2.me/submissions/7a0b6c29-b828-4942-adcf-c92b7d462b61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (s : ℕ → ℝ≥0) (hMono : Monotone s)
    (N : ℕ) (ω : Ω)
    (hInside : ∀ i < N, 0 < riskProcess X x D (s i) ω ∧
      ENNReal.ofReal (riskProcess X x D (s i) ω) < C)
    (hPay : ∀ i < N, D (s i) ω ≤ D (s (i + 1)) ω) :
    (∑ i ∈ Finset.range N,
      Real.exp (-(q * (s i : ℝ))) *
        (((s (i + 1) : ℝ) - (s i : ℝ)) *
          (X.generator w (riskProcess X x D (s i) ω) -
            q * w (riskProcess X x D (s i) ω)) +
        (D (s (i + 1)) ω - D (s i) ω) *
          (1 - deriv w (riskProcess X x D (s i) ω)))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  obtain ⟨hPos, hCap⟩ := hInside i (Finset.mem_range.mp hi)
  have hGenerator :
      X.generator w (riskProcess X x D (s i) ω) -
        q * w (riskProcess X x D (s i) ω) ≤ 0 :=
    (hw_gen _ hPos hCap).2
  have hGradient :
      1 - deriv w (riskProcess X x D (s i) ω) ≤ 0 :=
    sub_nonpos.mpr (hw_grad _ hPos hCap)
  have hStep : 0 ≤ (s (i + 1) : ℝ) - (s i : ℝ) := by
    apply sub_nonneg.mpr
    exact_mod_cast hMono (Nat.le_succ i)
  have hPayStep : 0 ≤ D (s (i + 1)) ω - D (s i) ω :=
    sub_nonneg.mpr (hPay i (Finset.mem_range.mp hi))
  have hTimePart :
      ((s (i + 1) : ℝ) - (s i : ℝ)) *
        (X.generator w (riskProcess X x D (s i) ω) -
          q * w (riskProcess X x D (s i) ω)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hStep hGenerator
  have hDividendPart :
      (D (s (i + 1)) ω - D (s i) ω) *
        (1 - deriv w (riskProcess X x D (s i) ω)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hPayStep hGradient
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) (add_nonpos hTimePart hDividendPart)