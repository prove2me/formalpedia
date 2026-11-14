-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:41:41.120443+00:00
-- url     : https://prove2.me/submissions/fe40c002-8a41-4652-8595-a97b481c5ff3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

/-- Restriction to a measurable submask preserves nonnegative finite source
integrability and vanishing expectation, even with sample-dependent masks. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Finset ℕ)
    (A B : ℕ → ℕ → Ω → Prop)
    [∀ m i, DecidablePred (A m i)] [∀ m i, DecidablePred (B m i)]
    (f : ℕ → ℕ → Ω → ℝ)
    (hBA : ∀ m i ω, B m i ω → A m i ω)
    (hfNonneg : ∀ m i ω, 0 ≤ f m i ω)
    (hfMeas : ∀ m i, Measurable (f m i))
    (hBMeas : ∀ m i, MeasurableSet {ω : Ω | B m i ω})
    (hAI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, if A m i ω then f m i ω else 0) P)
    (hALim : Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, if A m i ω then f m i ω else 0) ∂P)
      atTop (𝓝 (0 : ℝ))) :
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, if B m i ω then f m i ω else 0) P) ∧
    Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, if B m i ω then f m i ω else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let F : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ S m, if B m i ω then f m i ω else 0
  let G : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ S m, if A m i ω then f m i ω else 0
  have hFm (m : ℕ) : Measurable (F m) := by
    dsimp [F]
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hBMeas m i) (hfMeas m i) measurable_const
  have hPoint (m : ℕ) (ω : Ω) :
      0 ≤ F m ω ∧ F m ω ≤ G m ω := by
    constructor
    · dsimp [F]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs
      · exact hfNonneg m i ω
      · positivity
    · dsimp [F,G]
      apply Finset.sum_le_sum
      intro i hi
      by_cases hb : B m i ω
      · have ha : A m i ω := hBA m i ω hb
        simp only [if_pos hb,if_pos ha]
        exact le_refl _
      · by_cases ha : A m i ω
        · simp only [if_neg hb,if_pos ha]
          exact hfNonneg m i ω
        · simp only [if_neg hb,if_neg ha]
          exact le_refl _
  have hGpos (m : ℕ) (ω : Ω) : 0 ≤ G m ω := by
    dsimp [G]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact hfNonneg m i ω
    · positivity
  have hBI (m : ℕ) : Integrable (F m) P := by
    apply (hAI m).mono' (hFm m).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      have h := hPoint m ω
      simpa only [Real.norm_eq_abs,abs_of_nonneg h.1,
        abs_of_nonneg (hGpos m ω)] using h.2)
  have hUpper (m : ℕ) :
      (∫ ω, F m ω ∂P) ≤ (∫ ω, G m ω ∂P) :=
    integral_mono (hBI m) (hAI m) (fun ω => (hPoint m ω).2)
  change (∀ m, Integrable (F m) P) ∧
    Tendsto (fun m => ∫ ω, F m ω ∂P) atTop (𝓝 (0 : ℝ))
  refine ⟨hBI,?_⟩
  have hZero : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hZero hALim
    (Filter.Eventually.of_forall (fun m =>
      integral_nonneg (fun ω => (hPoint m ω).1)))
    (Filter.Eventually.of_forall hUpper)
