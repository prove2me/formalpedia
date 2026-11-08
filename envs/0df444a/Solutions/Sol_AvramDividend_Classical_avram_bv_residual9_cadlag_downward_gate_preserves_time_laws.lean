-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_cadlag_downward_gate_preserves_time_laws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:46:38.174206+00:00
-- url     : https://prove2.me/submissions/b6b8abdd-03ae-46c1-9c56-8334740f22eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_ProbabilityTheory_isCadlag_const
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (G : Set Ω)
    (hGmeas : MeasurableSet G) (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hMeas : ∀ t, Measurable (X t))
    (hCad : ∀ ω ∈ G, IsCadlag (fun t : ℝ≥0 => X t ω))
    (hDown : ∀ ω ∈ G, ∀ t : ℝ≥0, 0 < t →
      X t ω ≤ Function.leftLim (fun s : ℝ≥0 => X s ω) t) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, IsCadlag (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ ω (t : ℝ≥0), 0 < t →
        Y t ω ≤ Function.leftLim (fun s : ℝ≥0 => Y s ω) t) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[P] X t) := by
  classical
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then X t ω else 0
  refine ⟨Y, ?_, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ G
    · have heq : (fun t : ℝ≥0 => Y t ω) = fun t => X t ω := by
        funext t
        simp [Y, hω]
      rw [heq]
      exact hCad ω hω
    · have heq : (fun t : ℝ≥0 => Y t ω) = fun _ => (0 : ℝ) := by
        funext t
        simp [Y, hω]
      rw [heq]
      exact isCadlag_const
  · intro ω t ht
    change (fun s : ℝ≥0 => Y s ω) t ≤
      Function.leftLim (fun s : ℝ≥0 => Y s ω) t
    by_cases hω : ω ∈ G
    · have heq : (fun s : ℝ≥0 => Y s ω) = fun s => X s ω := by
        funext s
        simp [Y, hω]
      rw [heq]
      exact hDown ω hω t ht
    · have heq : (fun s : ℝ≥0 => Y s ω) = fun _ => (0 : ℝ) := by
        funext s
        simp [Y, hω]
      rw [heq]
      have hconst : Function.leftLim (fun _ : ℝ≥0 => (0 : ℝ)) t = 0 := by
        exact (continuous_const.continuousWithinAt.leftLim_eq)
      simp [hconst]
  · intro t
    change Measurable (fun ω => if ω ∈ G then X t ω else (0 : ℝ))
    exact Measurable.ite hGmeas (hMeas t) measurable_const
  · intro t
    filter_upwards [hGae] with ω hω
    simp [Y, hω]
