-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_two_positive_source_errors_mean_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:42:20.397916+00:00
-- url     : https://prove2.me/submissions/856d989a-5b53-497d-9e89-3b30b96058c5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_centred_pathwise_error_vanishing_mean_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F B M ErrCell ErrContact : ℕ → Ω → ℝ) (k : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hBI : ∀ n, Integrable (B n) P)
    (hMI : ∀ n, Integrable (M n) P)
    (hMean : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hCellI : ∀ n, Integrable (fun ω => max (ErrCell n ω) 0) P)
    (hContactI : ∀ n, Integrable (fun ω => max (ErrContact n ω) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ k + (M n ω + B n ω) +
        max (ErrCell n ω) 0 + max (ErrContact n ω) 0)
    (hCell : Tendsto (fun n => ∫ ω, max (ErrCell n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hContact : Tendsto (fun n => ∫ ω, max (ErrContact n ω) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun n => max ((∫ ω, F n ω ∂P) - k -
        (∫ ω, B n ω ∂P)) 0) atTop (nhds (0 : ℝ)) := by
  let Err : ℕ → Ω → ℝ := fun n ω =>
    max (ErrCell n ω) 0 + max (ErrContact n ω) 0
  have hErrNonneg (n : ℕ) (ω : Ω) : 0 ≤ Err n ω :=
    add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hErrMax (n : ℕ) :
      (fun ω => max (Err n ω) 0) =
        (fun ω => max (ErrCell n ω) 0 +
          max (ErrContact n ω) 0) := by
    funext ω
    rw [max_eq_left (hErrNonneg n ω)]
  have hErrI (n : ℕ) :
      Integrable (fun ω => max (Err n ω) 0) P := by
    rw [hErrMax]
    exact (hCellI n).add (hContactI n)
  have hErrBudget (n : ℕ) :
      ∀ᵐ ω ∂P, F n ω ≤
        k + (M n ω + B n ω) + max (Err n ω) 0 := by
    filter_upwards [hBudget n] with ω hω
    rw [max_eq_left (hErrNonneg n ω)]
    simpa only [Err, add_assoc] using hω
  have hErrIntegral (n : ℕ) :
      (∫ ω, max (Err n ω) 0 ∂P) =
        (∫ ω, max (ErrCell n ω) 0 ∂P) +
          (∫ ω, max (ErrContact n ω) 0 ∂P) := by
    rw [hErrMax]
    exact integral_add (hCellI n) (hContactI n)
  have hErrT :
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
        atTop (nhds (0 : ℝ)) := by
    have hEq :
        (fun n => ∫ ω, max (Err n ω) 0 ∂P) =
          (fun n =>
            (∫ ω, max (ErrCell n ω) 0 ∂P) +
            (∫ ω, max (ErrContact n ω) 0 ∂P)) := by
      funext n
      exact hErrIntegral n
    rw [hEq]
    simpa using hCell.add hContact
  exact avram_p3_comp8_centred_pathwise_error_vanishing_mean_gap
    P F B M Err k hFI hBI hMI hMean hErrI hErrBudget hErrT
