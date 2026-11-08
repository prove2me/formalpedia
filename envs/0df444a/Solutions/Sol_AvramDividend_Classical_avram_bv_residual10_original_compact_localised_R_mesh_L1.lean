-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_compact_localised_R_mesh_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:03:08.364903+00:00
-- url     : https://prove2.me/submissions/4d833c15-c985-4c09-be5b-39fb515a17d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_clipped_weighted_R_mesh_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On a measurable compact-localisation event, a deterministic coefficient
bound gives integrability of the untruncated original raw residual sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ) (ha : ∀ i, Measurable (fun ω => a ω i))
    (A : Set Ω) (hA : MeasurableSet A)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ ω ∈ A, ∀ i ∈ Finset.range (n + 1), |a ω i| ≤ K) :
    Integrable (fun ω =>
      if ω ∈ A then
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
        let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
        ∑ i ∈ Finset.range (n + 1),
          a ω i * (R (u n i) - R (u n (i + 1)))
      else 0) P := by
  classical
  let f : Ω → ℝ := fun ω =>
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    ∑ i ∈ Finset.range (n + 1),
      (if |a ω i| ≤ K then a ω i else 0) *
        (R (u n i) - R (u n (i + 1)))
  have hf : Integrable f P := by
    exact avram_bv_residual10_original_clipped_weighted_R_mesh_L1
      X hX hBV T u n hu hu0 huT a ha K hK
  have hsame : (fun ω =>
      if ω ∈ A then
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
        let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
        ∑ i ∈ Finset.range (n + 1),
          a ω i * (R (u n i) - R (u n (i + 1)))
      else 0) = A.indicator f := by
    funext ω
    by_cases hw : ω ∈ A
    · simp only [if_pos hw, Set.indicator_of_mem hw, f]
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (hb ω hw i hi)]
    · simp only [if_neg hw, Set.indicator_of_notMem hw]
  rw [hsame]
  exact hf.indicator hA
