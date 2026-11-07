-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_centred_pathwise_error_vanishing_mean_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:56:25.758249+00:00
-- url     : https://prove2.me/submissions/76912f5d-d812-486f-8802-36802ae1a1f7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_centred_pathwise_budget_expected_gap_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
noncomputable section

/- Genuine source-error convergence transfers into the signed mean gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F B M Err : ℕ → Ω → ℝ) (k : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hBI : ∀ n, Integrable (B n) P)
    (hMI : ∀ n, Integrable (M n) P)
    (hMean : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hEI : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ k + (M n ω + B n ω) + max (Err n ω) 0)
    (hErr : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun n => max ((∫ ω, F n ω ∂P) -
        k - (∫ ω, B n ω ∂P)) 0) atTop (nhds (0 : ℝ)) := by
  have hPos (n : ℕ) :
      0 ≤ max ((∫ ω, F n ω ∂P) - k -
          (∫ ω, B n ω ∂P)) 0 :=
    le_max_right _ _
  have hUpper (n : ℕ) :
      max ((∫ ω, F n ω ∂P) - k -
          (∫ ω, B n ω ∂P)) 0 ≤
        (∫ ω, max (Err n ω) 0 ∂P) :=
    avram_p3_comp8_centred_pathwise_budget_expected_gap_bound
      P (F n) (B n) (M n) (Err n) k
      (hFI n) (hBI n) (hMI n) (hMean n)
      (hEI n) (hBudget n)
  exact squeeze_zero hPos hUpper hErr
