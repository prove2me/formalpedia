-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen16_gate_ae_cadlag_paths_to_all_paths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:44:00.995721+00:00
-- url     : https://prove2.me/submissions/33153e49-fc2a-49aa-afa7-acfa62588435

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_ProbabilityTheory_isCadlag_const

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal
noncomputable section

/-- Gate an almost-sure cadlag process on a measurable good event to obtain
literal cadlag paths, preserving each time marginal almost everywhere. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (G : Set Ω)
    (hGmeas : MeasurableSet G) (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hMeas : ∀ t, Measurable (X t))
    (hCad : ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => X t ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, IsCadlag (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[P] X t) := by
  classical
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then X t ω else 0
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ G
    · have heq : (fun t : ℝ≥0 => Y t ω) = (fun t => X t ω) := by
        funext t
        simp [Y, hω]
      rw [heq]
      exact hCad ω hω
    · have heq : (fun t : ℝ≥0 => Y t ω) = (fun _ => (0 : ℝ)) := by
        funext t
        simp [Y, hω]
      rw [heq]
      exact isCadlag_const
  · intro t
    change Measurable (fun ω => if ω ∈ G then X t ω else (0 : ℝ))
    exact Measurable.ite hGmeas (hMeas t) measurable_const
  · intro t
    filter_upwards [hGae] with ω hω
    simp [Y, hω]
