-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_signed_grid_envelope_of_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:15:59.378218+00:00
-- url     : https://prove2.me/submissions/622caa71-abb7-4016-9f62-880748d8e1f9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_fatou_real_grid_certificate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An already established physical-grid expectation upper bound generates
    the signed F/M/B witness interface without requiring a new stochastic
    decomposition identity; the Fatou lower limit remains source-bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (c : ℝ)
    (F : ℕ → Ω → ℝ) (L : Ω → ℝ≥0∞)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hConstI : Integrable (fun _ : Ω => c) P)
    (hConstMean : (∫ _ω : Ω, c ∂P) = c)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ c)
    (hFatou : ∀ᵐ ω ∂P,
      L ω ≤ liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    ∃ F' M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n)) ∧
      (∀ n, Integrable (F' n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F' n ω ≤ c + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        L ω ≤ liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by
  refine ⟨F, (fun n ω => F n ω - c), (fun _ _ => 0),
    hFm, hFi, hFn, ?_, ?_, hFatou⟩
  · intro n
    have hInt : Integrable (fun ω => F n ω - c) P :=
      (hFi n).sub hConstI
    constructor
    · simpa using hInt
    · have hBound : (∫ ω, F n ω - c ∂P) ≤ 0 := by
        rw [integral_sub (hFi n) hConstI, hConstMean]
        linarith [hMean n]
      simpa using hBound
  · intro n
    filter_upwards [] with ω
    linarith
