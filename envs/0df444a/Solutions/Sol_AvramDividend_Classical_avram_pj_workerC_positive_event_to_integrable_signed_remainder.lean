-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_positive_event_to_integrable_signed_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:06:26.175734+00:00
-- url     : https://prove2.me/submissions/85346bb3-d3e1-4cf5-b100-86ec22ffc98e

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Set Ω) (hS : MeasurableSet S)
    (G U : Ω → ℝ) (ε : ℝ)
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hOff : ∀ ω, ω ∉ S → G ω - U ω ≤ 0)
    (hSmall : (∫ ω in S, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε) :
    ∃ E R : Ω → ℝ,
      Integrable E P ∧
      (∫ ω, |E ω| ∂P) ≤ ε ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, G ω - U ω ≤ E ω + R ω) := by 
  let f : Ω → ℝ := fun ω => max (0 : ℝ) (G ω - U ω)
  let E : Ω → ℝ := S.indicator f
  let R : Ω → ℝ := fun ω => G ω - U ω - E ω
  have hfI : Integrable f P := by
    have hpoint : f = (fun ω => (|G ω - U ω| + (G ω - U ω)) / 2) := by
      funext ω
      dsimp [f]
      rcases le_total (0 : ℝ) (G ω - U ω) with hp | hp
      · rw [max_eq_right hp, abs_of_nonneg hp]
        ring
      · rw [max_eq_left hp, abs_of_nonpos hp]
        ring
    rw [hpoint]
    exact (hGapI.abs.add hGapI).div_const 2
  have hEI : Integrable E P := hfI.indicator hS
  have hEpos : ∀ ω, 0 ≤ E ω := by
    intro ω
    by_cases hmem : ω ∈ S
    · simpa [E, f, Set.indicator_of_mem hmem] using
        (le_max_left (0 : ℝ) (G ω - U ω))
    · simp [E, Set.indicator_of_notMem hmem]
  have hEabs : (fun ω => |E ω|) = E := by
    funext ω
    exact abs_of_nonneg (hEpos ω)
  have hEbound : (∫ ω, |E ω| ∂P) ≤ ε := by
    rw [hEabs]
    change (∫ ω, S.indicator f ω ∂P) ≤ ε
    rw [integral_indicator hS]
    exact hSmall
  refine ⟨E, R, hEI, hEbound, ?_, ?_⟩
  · filter_upwards [] with ω
    change G ω - U ω - E ω ≤ 0
    apply sub_nonpos.mpr
    by_cases hmem : ω ∈ S
    · change G ω - U ω ≤ S.indicator f ω
      rw [Set.indicator_of_mem hmem]
      exact le_max_right _ _
    · change G ω - U ω ≤ S.indicator f ω
      rw [Set.indicator_of_notMem hmem]
      simpa using hOff ω hmem
  · filter_upwards [] with ω
    change G ω - U ω ≤ E ω + (G ω - U ω - E ω)
    linarith
