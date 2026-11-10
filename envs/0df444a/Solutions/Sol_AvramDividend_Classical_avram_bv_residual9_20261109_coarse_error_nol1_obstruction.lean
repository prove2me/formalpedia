-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_20261109_coarse_error_nol1_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:39:14.7492+00:00
-- url     : https://prove2.me/submissions/e48875e3-e196-432b-abcd-2065583948d9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_residual14_positive_mean_deficit_centring_obstruction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
noncomputable section

/-- A negative coarse-grid budget requires a non-vanishing positive error,
even when the signed budget is not integrable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (c ε L η : ℝ) (hη : 0 < η) (hgap : c + η ≤ ε * L)
    (F M B Err : ℕ → Ω → ℝ)
    (hF : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hM : ∀ n, Integrable (M n) P)
    (hM0 : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ c + M n ω + B n ω + max (Err n ω) 0)
    (hBpath : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ -(ε * L)) :
    ¬ Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  intro hlim
  have hLower : ∀ n, ∀ᵐ ω ∂P,
      η ≤ M n ω + max (Err n ω) 0 := by
    intro n
    filter_upwards [hF n, hBudget n, hBpath n] with ω hf hb hp
    linarith
  have hGPos : 0 < ∫ ω : Ω, (η : ℝ) ∂P := by
    simpa using hη
  exact avram_residual14_positive_mean_deficit_centring_obstruction
    P (fun _ => η) (integrable_const _) hGPos M Err
    (fun n => ⟨hM n, hM0 n⟩) hErr hlim hLower
