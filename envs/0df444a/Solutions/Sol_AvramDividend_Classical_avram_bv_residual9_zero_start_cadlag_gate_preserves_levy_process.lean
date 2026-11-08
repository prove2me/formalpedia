-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_zero_start_cadlag_gate_preserves_levy_process
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:10:28.0632+00:00
-- url     : https://prove2.me/submissions/34d17863-21d2-482b-a1cb-79d789edc265

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_isLevyProcess_of_ae_time_sections
import Theorems.Thm_ProbabilityTheory_isCadlag_const
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P) (hX0 : ∀ ω, X 0 ω = 0)
    (G : Set Ω) (hGmeas : MeasurableSet G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hXm : ∀ t, Measurable (X t))
    (hGcad : ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => X t ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsLevyProcess Y P ∧
      (∀ ω, IsCadlag (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[P] X t) := by
  classical
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then X t ω else 0
  have hYcad : ∀ ω, IsCadlag (fun t : ℝ≥0 => Y t ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · have heq : (fun t : ℝ≥0 => Y t ω) = (fun t => X t ω) := by
        funext t
        simp [Y, hω]
      rw [heq]
      exact hGcad ω hω
    · have heq : (fun t : ℝ≥0 => Y t ω) = (fun _ => (0 : ℝ)) := by
        funext t
        simp [Y, hω]
      rw [heq]
      exact isCadlag_const
  have hYm : ∀ t, Measurable (Y t) := by
    intro t
    change Measurable (fun ω => if ω ∈ G then X t ω else (0 : ℝ))
    exact Measurable.ite hGmeas (hXm t) measurable_const
  have hY0 : ∀ ω, Y 0 ω = 0 := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa [Y, hω] using hX0 ω
    · simp [Y, hω]
  have hYae : ∀ t, Y t =ᵐ[P] X t := by
    intro t
    filter_upwards [hGae] with ω hω
    simp [Y, hω]
  have hYaeCad : ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => Y t ω) :=
    Filter.Eventually.of_forall hYcad
  exact ⟨Y, avram_bv_residual9_isLevyProcess_of_ae_time_sections
    X Y hX hY0 hYm hYaeCad hYae, hYcad, hYm, hYae⟩
