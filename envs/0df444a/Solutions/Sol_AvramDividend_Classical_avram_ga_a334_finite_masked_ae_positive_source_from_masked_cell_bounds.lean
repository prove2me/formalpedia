-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a334_finite_masked_ae_positive_source_from_masked_cell_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:41:21.505636+00:00
-- url     : https://prove2.me/submissions/23a66220-02f7-4688-a73c-87a701f57923

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a245_finite_masked_combined_one_sided_cell_bounds_sum_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (f g : ℕ → Ω → ℝ)
    (hG : ∀ᵐ ω ∂P, ∀ i ∈ S,
      A i ω → 0 ≤ g i ω)
    (hCell : ∀ᵐ ω ∂P, ∀ i ∈ S,
      A i ω → max (f i ω) 0 ≤ g i ω) :
    ∀ᵐ ω ∂P,
      max (∑ i ∈ S, if A i ω then f i ω else 0) 0 ≤
      ∑ i ∈ S, if A i ω then g i ω else 0 := by
  classical
  filter_upwards [hG,hCell] with ω hg hc
  let F : ℕ → ℝ := fun i =>
    if A i ω then f i ω else 0
  let G : ℕ → ℝ := fun i =>
    if A i ω then g i ω else 0
  have hGp : ∀ i ∈ S, 0 ≤ G i := by
    intro i hi
    by_cases ha : A i ω
    · simpa only [G,if_pos ha] using hg i hi ha
    · simp only [G,if_neg ha,le_refl]
  have hBound : ∀ i ∈ S, max (F i) 0 ≤ G i := by
    intro i hi
    by_cases ha : A i ω
    · simpa only [F,G,if_pos ha] using hc i hi ha
    · simp only [F,G,if_neg ha,max_self,le_refl]
  have h := avram_ga_a245_finite_masked_combined_one_sided_cell_bounds_sum_positive
    S (fun _ : ℕ => True) F G hGp hBound
  simpa only [if_true,F,G] using h
