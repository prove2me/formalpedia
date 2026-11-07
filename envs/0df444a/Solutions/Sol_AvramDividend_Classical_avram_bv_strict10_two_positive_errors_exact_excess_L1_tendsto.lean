-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict10_two_positive_errors_exact_excess_L1_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:37:44.791088+00:00
-- url     : https://prove2.me/submissions/9c21d06c-bde0-49d6-a7f3-ed4468967e7c

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Two separately controlled original contact and C1 errors yield
    an integrable exact signed-source positive deficit tending to zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (F M B ErrCell ErrContact : ℕ → Ω → ℝ) (base : ℝ)
    (hCell : ∀ n, Integrable (fun ω => max (ErrCell n ω) 0) P)
    (hContact : ∀ n, Integrable (fun ω => max (ErrContact n ω) 0) P)
    (hExcessMeas : ∀ n, AEStronglyMeasurable
      (fun ω => max (F n ω - (base + (M n ω + B n ω))) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ base + (M n ω + B n ω) +
        max (ErrCell n ω) 0 + max (ErrContact n ω) 0)
    (hCellZero : Tendsto
      (fun n => ∫ ω, max (ErrCell n ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hContactZero : Tendsto
      (fun n => ∫ ω, max (ErrContact n ω) 0 ∂P) atTop (nhds (0 : ℝ))) :
    (∀ n, Integrable
      (fun ω => max (F n ω - (base + (M n ω + B n ω))) 0) P) ∧
    Tendsto (fun n =>
      ∫ ω, max (F n ω - (base + (M n ω + B n ω))) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hSingle (n : ℕ) :=
    AvramDividend.Classical.avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
      P (F n) (M n) (B n) (ErrCell n) (ErrContact n) base
      (hCell n) (hContact n) (hExcessMeas n) (hBudget n)
  refine ⟨(fun n => (hSingle n).1), ?_⟩
  have hLower (n : ℕ) : (0 : ℝ) ≤
      ∫ ω, max (F n ω - (base + (M n ω + B n ω))) 0 ∂P :=
    integral_nonneg (fun ω => le_max_right _ _)
  have hUpper (n : ℕ) :
      (∫ ω, max (F n ω - (base + (M n ω + B n ω))) 0 ∂P) ≤
        (∫ ω, max (ErrCell n ω) 0 ∂P) +
          (∫ ω, max (ErrContact n ω) 0 ∂P) :=
    (hSingle n).2
  exact squeeze_zero hLower hUpper (by
    simpa only [zero_add] using (hCellZero.add hContactZero))
