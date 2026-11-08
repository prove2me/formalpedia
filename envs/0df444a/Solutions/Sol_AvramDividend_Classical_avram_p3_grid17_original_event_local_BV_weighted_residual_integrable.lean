-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid17_original_event_local_BV_weighted_residual_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:48:02.69794+00:00
-- url     : https://prove2.me/submissions/ac8139f6-b5e9-401b-8744-257894b330c2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_clipped_weighted_R_mesh_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Clipped original BV mesh integrability transfers to the same source
    on a measurable event where all genuine coefficients are bounded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ)
    (hMeasA : ∀ i, Measurable (fun ω => a ω i))
    (s : Set Ω) (hs : MeasurableSet s)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω ∈ s, ∀ i ∈ Finset.range (n + 1), |a ω i| ≤ K) :
    Integrable (fun ω => if ω ∈ s then
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
      ∑ i ∈ Finset.range (n + 1),
        a ω i * (R (u n i) - R (u n (i + 1)))
    else 0) P := by
  classical
  let R : Ω → ℝ≥0 → ℝ := fun ω t =>
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0)
  have hclip : Integrable (fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        (if |a ω i| ≤ K then a ω i else 0) *
          (R ω (u n i) - R ω (u n (i + 1)))) P := by
    simpa only [R] using
      (avram_bv_residual10_original_clipped_weighted_R_mesh_L1
        X hX hBV T u n hu hu0 huT a hMeasA K hK)
  have hsame (ω : Ω) (hω : ω ∈ s) :
      (∑ i ∈ Finset.range (n + 1),
        a ω i * (R ω (u n i) - R ω (u n (i + 1)))) =
      (∑ i ∈ Finset.range (n + 1),
        (if |a ω i| ≤ K then a ω i else 0) *
          (R ω (u n i) - R ω (u n (i + 1)))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (hBound ω hω i hi)]
  have heq :
      (fun ω => if ω ∈ s then
        ∑ i ∈ Finset.range (n + 1),
          a ω i * (R ω (u n i) - R ω (u n (i + 1))) else 0) =
      (fun ω => if ω ∈ s then
        ∑ i ∈ Finset.range (n + 1),
          (if |a ω i| ≤ K then a ω i else 0) *
            (R ω (u n i) - R ω (u n (i + 1))) else 0) := by
    funext ω
    by_cases hω : ω ∈ s
    · simp only [if_pos hω, hsame ω hω]
    · simp only [if_neg hω]
  change Integrable (fun ω => if ω ∈ s then
    ∑ i ∈ Finset.range (n + 1),
      a ω i * (R ω (u n i) - R ω (u n (i + 1))) else 0) P
  rw [heq]
  change Integrable (s.indicator (fun ω =>
    ∑ i ∈ Finset.range (n + 1),
      (if |a ω i| ≤ K then a ω i else 0) *
        (R ω (u n i) - R ω (u n (i + 1))))) P
  exact hclip.indicator hs
