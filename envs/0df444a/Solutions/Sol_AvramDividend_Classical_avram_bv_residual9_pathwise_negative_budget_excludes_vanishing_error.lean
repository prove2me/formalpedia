-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_pathwise_negative_budget_excludes_vanishing_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:05:26.670382+00:00
-- url     : https://prove2.me/submissions/fe42f427-2325-4eb2-8883-c5070f18fada

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_negative_budget_excludes_vanishing_positive_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (c ε L η : ℝ) (hη : 0 < η) (hgap : c + η ≤ ε * L)
    (F M B Err : ℕ → Ω → ℝ)
    (hF : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hM : ∀ n, Integrable (M n) P)
    (hM0 : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hB : ∀ n, Integrable (B n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ c + M n ω + B n ω + max (Err n ω) 0)
    (hBpath : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ -(ε * L)) :
    ¬ Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by
  apply avram_bv_residual9_negative_budget_excludes_vanishing_positive_error
    c η hη F M B Err hF hM hM0 hB hErr hBudget
  intro n
  have hle : (∫ ω, B n ω ∂P) ≤ ∫ _ : Ω, (-(ε * L) : ℝ) ∂P :=
    integral_mono_ae (hB n) (integrable_const _) (hBpath n)
  have hconst : (∫ _ : Ω, (-(ε * L) : ℝ) ∂P) = -(ε * L) := by simp
  linarith
