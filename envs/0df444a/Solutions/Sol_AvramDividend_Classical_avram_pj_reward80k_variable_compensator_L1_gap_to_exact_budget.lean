-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward80k_variable_compensator_L1_gap_to_exact_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:06:24.125313+00:00
-- url     : https://prove2.me/submissions/df756d3c-29e2-4dd8-a9e3-947b74d206e3

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Epsilon-dependent true compensator bands suffice for an exact stopped
reward mean inequality when each signed generator expectation is nonpositive. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (G : Ω → ℝ)
    (hGI : Integrable G P)
    (hSource : ∀ ε : ℝ, 0 < ε →
      ∃ H : Ω → ℝ,
        Integrable H P ∧
        (∫ ω, H ω ∂P) ≤ 0 ∧
        (∫ ω, max (0 : ℝ) (G ω - (a + H ω)) ∂P) ≤ ε) :
    (∫ ω, G ω ∂P) ≤ a := by
  by_contra hNot
  have hp : 0 < (∫ ω, G ω ∂P) - a := by linarith
  obtain ⟨H, hHI, hHmean, hGap⟩ :=
    hSource (((∫ ω, G ω ∂P) - a) / 2) (by positivity)
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
  have hBound :=
    (integral_mono_ae hDI hPosI (Filter.Eventually.of_forall
      (fun ω => le_max_right (0 : ℝ) (G ω - (a + H ω))))).trans hGap
  rw [hMean] at hBound
  linarith
