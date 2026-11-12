-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_original_gaussian_residual_initial_zero_of_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:58:25.990945+00:00
-- url     : https://prove2.me/submissions/eea37ca5-fe8e-4bcb-af2a-ff4382a5e910

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (R : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * a ^ 2) :
    ∀ᵐ ω ∂P, R 0 ω = 0 := by
  obtain ⟨hI, hEq⟩ := hRbracket 0
  have hZero : (∫ ω, (R 0 ω) ^ 2 ∂P) = 0 := by
    simpa using hEq
  have hn : (0 : Ω → ℝ) ≤ fun ω => (R 0 ω) ^ 2 := by
    intro ω
    exact sq_nonneg _
  have hs :=
    (integral_eq_zero_iff_of_nonneg hn hI).mp hZero
  filter_upwards [hs] with ω hw
  have hsq : (R 0 ω) ^ 2 = 0 := by
    simpa using hw
  nlinarith [sq_nonneg (R 0 ω)]
