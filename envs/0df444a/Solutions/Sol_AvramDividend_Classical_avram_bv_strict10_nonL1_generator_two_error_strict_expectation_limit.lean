-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict10_nonL1_generator_two_error_strict_expectation_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:38:00.877048+00:00
-- url     : https://prove2.me/submissions/42d7b971-389f-4f39-8744-6646fb49f3a6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_discard_nonL1_negative_generator_before_expectation
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Nonintegrable signed BV generator is discarded pointwise; two
    vanishing positive expectation errors give eventual strict budgets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F M B ErrCell ErrContact : ℕ → Ω → ℝ) (base : ℝ)
    (hM : ∀ n, Integrable (M n) P)
    (hMzero : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hCell : ∀ n, Integrable (fun ω => max (ErrCell n ω) 0) P)
    (hContact : ∀ n, Integrable (fun ω => max (ErrContact n ω) 0) P)
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) P)
    (hFnonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hBnonpos : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ base + (M n ω + B n ω) +
        max (ErrCell n ω) 0 + max (ErrContact n ω) 0)
    (hCellZero : Tendsto
      (fun n => ∫ ω, max (ErrCell n ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hContactZero : Tendsto
      (fun n => ∫ ω, max (ErrContact n ω) 0 ∂P) atTop (nhds (0 : ℝ))) :
    (∀ n, Integrable (F n) P) ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, (∫ ω, F n ω ∂P) ≤ base + ε) := by
  have hSingle (n : ℕ) :=
    AvramDividend.Classical.avram_bv_strict10_discard_nonL1_negative_generator_before_expectation
      P (F n) (M n) (B n) (ErrCell n) (ErrContact n) base
        (hM n) (hMzero n) (hCell n) (hContact n)
        (hFmeas n) (hFnonneg n) (hBnonpos n) (hBudget n)
  refine ⟨(fun n => (hSingle n).1), ?_⟩
  intro ε hε
  have hZero : Tendsto (fun n =>
      (∫ ω, max (ErrCell n ω) 0 ∂P) +
      (∫ ω, max (ErrContact n ω) 0 ∂P))
      atTop (nhds (0 : ℝ)) := by
    simpa only [zero_add] using (hCellZero.add hContactZero)
  have hEvent : ∀ᶠ n in atTop,
      (∫ ω, max (ErrCell n ω) 0 ∂P) +
      (∫ ω, max (ErrContact n ω) 0 ∂P) < ε :=
    hZero.eventually (isOpen_Iio.mem_nhds hε)
  filter_upwards [hEvent] with n hn
  have hBound := (hSingle n).2
  linarith
