-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict10_two_scale_signed_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:33:41.279467+00:00
-- url     : https://prove2.me/submissions/cb94038a-590f-42fd-af13-88f7492e76d7

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_discard_nonL1_negative_generator_before_expectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- Two-scale strict expectation bound with a nonintegrable nonpositive source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F B : ℕ → Ω → ℝ)
    (M ErrCell ErrContact : ℕ → ℕ → Ω → ℝ)
    (η : ℕ → ℝ) (base : ℝ)
    (hM : ∀ n k, Integrable (M n k) P)
    (hMzero : ∀ n k, (∫ ω, M n k ω ∂P) = 0)
    (hCell : ∀ n k, Integrable (fun ω => max (ErrCell n k ω) 0) P)
    (hContact : ∀ n k, Integrable (fun ω => max (ErrContact n k ω) 0) P)
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) P)
    (hFnonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hBnonpos : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hBudget : ∀ n k, ∀ᵐ ω ∂P,
      F n ω ≤ base + (M n k ω + B n ω) +
        max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0)
    (hη : Tendsto η atTop (nhds (0 : ℝ)))
    (hErrors : ∀ n (ε : ℝ), 0 < ε →
      ∃ k : ℕ,
        (∫ ω, max (ErrCell n k ω) 0 ∂P) +
          (∫ ω, max (ErrContact n k ω) 0 ∂P) ≤ η n + ε) :
    (∀ n, Integrable (F n) P) ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, (∫ ω, F n ω ∂P) ≤ base + ε) := by
  have hOne (n k : ℕ) :=
    AvramDividend.Classical.avram_bv_strict10_discard_nonL1_negative_generator_before_expectation
      P (F n) (M n k) (B n) (ErrCell n k) (ErrContact n k) base
      (hM n k) (hMzero n k) (hCell n k) (hContact n k)
      (hFmeas n) (hFnonneg n) (hBnonpos n) (hBudget n k)
  refine ⟨fun n => (hOne n 0).1, ?_⟩
  intro ε hε
  have hηsmall : ∀ᶠ n in atTop, η n < ε / 2 :=
    hη.eventually (isOpen_Iio.mem_nhds (half_pos hε))
  filter_upwards [hηsmall] with n hn
  obtain ⟨k, hk⟩ := hErrors n (ε / 2) (by linarith)
  have hb := (hOne n k).2
  linarith
