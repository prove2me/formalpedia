-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_random_measure_double_monotone_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:40:54.398829+00:00
-- url     : https://prove2.me/submissions/87d4f7c6-81d9-42d4-93d5-23ae79111129

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Two monotone convergence steps for sample-dependent source jump measures;
outer measurability of each stochastic integral is required explicitly. -/
theorem solution
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (M : Ω → Measure α)
    (F : ℕ → Ω → α → ℝ≥0∞)
    (hF : ∀ ω n, Measurable (F n ω))
    (hOuter : ∀ n,
      Measurable (fun ω => (∫⁻ x, F n ω x ∂M ω)))
    (hMono : ∀ ω, Monotone (fun n => F n ω)) :
    (∫⁻ ω, (∫⁻ x, ⨆ n, F n ω x ∂M ω) ∂P) =
    ⨆ n, (∫⁻ ω, (∫⁻ x, F n ω x ∂M ω) ∂P) := by
  have hOuterMono :
      Monotone (fun n ω => (∫⁻ x, F n ω x ∂M ω)) := by
    intro n m hnm ω
    exact lintegral_mono (hMono ω hnm)
  calc
    (∫⁻ ω, (∫⁻ x, ⨆ n, F n ω x ∂M ω) ∂P) =
        (∫⁻ ω, ⨆ n, (∫⁻ x, F n ω x ∂M ω) ∂P) := by
          congr 1
          funext ω
          exact lintegral_iSup (hF ω) (hMono ω)
    _ = ⨆ n, (∫⁻ ω, (∫⁻ x, F n ω x ∂M ω) ∂P) :=
      lintegral_iSup hOuter hOuterMono
