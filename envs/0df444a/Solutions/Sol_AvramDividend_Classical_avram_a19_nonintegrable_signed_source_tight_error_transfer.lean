-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_nonintegrable_signed_source_tight_error_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T14:37:22.973199+00:00
-- url     : https://prove2.me/submissions/8457ed9e-2852-4c25-b353-6c7a89b2bd4b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_a19_tight_positive_excess_le_any_error

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

/-- Transfer vanishing positive error bounds without integrating the signed baseline. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F G Err : ℕ → Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun ω => max (F n ω - G n ω) 0) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hlim : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hbudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ G n ω + max (Err n ω) 0) :
    (∀ n, Integrable (fun ω => max (F n ω - G n ω) 0) P) ∧
    Tendsto (fun n => ∫ ω, max (F n ω - G n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hdom (n : ℕ) : ∀ᵐ ω ∂P,
      max (F n ω - G n ω) 0 ≤ max (Err n ω) 0 := by
    filter_upwards [hbudget n] with ω hω
    exact AvramDividend.Classical.avram_a19_tight_positive_excess_le_any_error
      (F n ω) (G n ω) (Err n ω) hω
  have hInt (n : ℕ) :
      Integrable (fun ω => max (F n ω - G n ω) 0) P := by
    refine (hErr n).mono' (hMeas n) ?_
    filter_upwards [hdom n] with ω hω
    have hF0 : 0 ≤ max (F n ω - G n ω) 0 := le_max_right _ _
    have hE0 : 0 ≤ max (Err n ω) 0 := le_max_right _ _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hF0,
      abs_of_nonneg hE0] using hω
  refine ⟨hInt, ?_⟩
  apply squeeze_zero
  · intro n
    exact integral_nonneg (fun ω => le_max_right (F n ω - G n ω) 0)
  · intro n
    exact integral_mono_ae (hInt n) (hErr n) (hdom n)
  · exact hlim
