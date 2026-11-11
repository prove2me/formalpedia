-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger67_original_clipped_gaussian_mesh_stops_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:19:40.814351+00:00
-- url     : https://prove2.me/submissions/9240e986-c8fe-4aab-b918-624b911b8ea9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- Every original clipped Gaussian source mesh endpoint is a bounded stopping
    time whose WithTop-valued clock is measurable on the original sample space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (n m : ℕ) (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    ∀ i : ℕ,
      IsStoppingTime 𝓕.rightCont (fun ω =>
        min (ρ ω : WithTop ℝ≥0) ((i : ℝ≥0) * Δ)) ∧
      Measurable (fun ω =>
        min (ρ ω : WithTop ℝ≥0) ((i : ℝ≥0) * Δ)) ∧
      (∀ ω, min ((i : ℝ≥0) * Δ) (ρ ω) ≤ (n : ℝ≥0)) := by
  intro Δ i
  have hs : IsStoppingTime 𝓕.rightCont (fun ω =>
      min (ρ ω : WithTop ℝ≥0) ((i : ℝ≥0) * Δ)) :=
    hρstop.min_const ((i : ℝ≥0) * Δ)
  have hmeas : Measurable (fun ω =>
      min (ρ ω : WithTop ℝ≥0) ((i : ℝ≥0) * Δ)) :=
    hs.measurable.mono hs.measurableSpace_le le_rfl
  refine ⟨hs, hmeas, ?_⟩
  intro ω
  exact (min_le_right _ _).trans (hρbound ω)
