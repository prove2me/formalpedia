-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward80j_positive_gap_to_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:05:26.206291+00:00
-- url     : https://prove2.me/submissions/fd5c1860-001d-45a4-97a1-4906acbe7250

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- A nonpositive compensator mean and vanishing expected positive reward
excess imply the original exact-clock HJB expected upper bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (G H : Ω → ℝ)
    (hGI : Integrable G P)
    (hHI : Integrable H P)
    (hHmean : (∫ ω, H ω ∂P) ≤ 0)
    (hGap : ∀ ε : ℝ, 0 < ε →
      (∫ ω, max (0 : ℝ) (G ω - (a + H ω)) ∂P) ≤ ε) :
    (∫ ω, G ω ∂P) ≤ a := by
  have hUI : Integrable (fun ω => a + H ω) P :=
    (integrable_const a).add hHI
  have hDI : Integrable (fun ω => G ω - (a + H ω)) P :=
    hGI.sub hUI
  have hPosEq :
      (fun ω => max (0 : ℝ) (G ω - (a + H ω))) =
        (fun ω => ((G ω - (a + H ω)) +
          |G ω - (a + H ω)|) / 2) := by
    funext ω
    rcases le_total (G ω - (a + H ω)) 0 with h | h
    · rw [max_eq_left h, abs_of_nonpos h]
      ring
    · rw [max_eq_right h, abs_of_nonneg h]
      ring
  have hPosI :
      Integrable (fun ω => max (0 : ℝ) (G ω - (a + H ω))) P := by
    rw [hPosEq]
    exact (hDI.add hDI.abs).div_const 2
  have hMean :
      (∫ ω, G ω - (a + H ω) ∂P) =
        (∫ ω, G ω ∂P) - a - (∫ ω, H ω ∂P) := by
    rw [integral_sub hGI hUI, integral_add (integrable_const a) hHI]
    simp
    ring
  by_contra hNot
  have hp : 0 < (∫ ω, G ω ∂P) - a := by linarith
  have hBound :=
    (integral_mono_ae hDI hPosI (Filter.Eventually.of_forall
      (fun ω => le_max_right (0 : ℝ) (G ω - (a + H ω))))).trans
      (hGap (((∫ ω, G ω ∂P) - a) / 2) (by positivity))
  rw [hMean] at hBound
  linarith
