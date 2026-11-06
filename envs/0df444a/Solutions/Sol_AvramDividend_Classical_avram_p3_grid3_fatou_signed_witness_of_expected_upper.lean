-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_fatou_signed_witness_of_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T01:09:18.589894+00:00
-- url     : https://prove2.me/submissions/53be11b5-dcd8-4696-b047-cd2e6659abea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- An exact expected upper reward bound gives an explicit signed Fatou witness. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (c : ℝ)
    (G : Ω → ℝ) (F : ℕ → Ω → ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hExpected : ∀ n, (∫ ω, F n ω ∂P) ≤ c)
    (hFatou : ∀ᵐ ω ∂P, ENNReal.ofReal (G ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    ∃ F' M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n)) ∧
      (∀ n, Integrable (F' n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P, F' n ω ≤ c + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P, ENNReal.ofReal (G ω) ≤
        liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by
  refine ⟨F, (fun n ω => F n ω - c), (fun _ _ => 0),
    hFm, hFi, hFn, ?_, ?_, hFatou⟩
  · intro n
    constructor
    · have hz : Integrable (fun ω => F n ω - c) P := by
        exact (hFi n).sub (integrable_const c)
      simpa only [add_zero] using hz
    · have hi : (∫ ω, F n ω - c ∂P) ≤ 0 := by
        rw [integral_sub (hFi n) (integrable_const c)]
        simpa using (sub_nonpos.mpr (hExpected n))
      simpa only [add_zero] using hi
  · intro n
    exact Filter.Eventually.of_forall (fun ω => by
      change F n ω ≤ c + ((F n ω - c) + 0)
      linarith)
