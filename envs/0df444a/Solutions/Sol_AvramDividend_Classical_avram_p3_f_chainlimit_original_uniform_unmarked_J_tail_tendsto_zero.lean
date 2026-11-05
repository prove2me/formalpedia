-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_unmarked_J_tail_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:37:53.841342+00:00
-- url     : https://prove2.me/submissions/b714b78b-4a54-47bc-86b8-61b745ac3aa1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_unmarked_finite_marks_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (hGrid : ∀ k i, i < n k → (u k) i ≤ (u k) (i + 1)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      ∀ (T : ℕ → Finset ℝ≥0)
        (hCover : ∀ k, ∀ v ∈ T k, ∃ i : ℕ,
          i < n k ∧ (u k) i < v ∧ v ≤ (u k) (i + 1))
        (hSeparate : ∀ k, ∀ v ∈ T k, ∀ z ∈ T k, ∀ i : ℕ,
          i < n k → (u k) i < v → v ≤ (u k) (i + 1) →
          (u k) i < z → z ≤ (u k) (i + 1) → v = z),
        Tendsto (fun k =>
          J ((u k) (n k)) - J ((u k) 0) -
            (T k).sum (fun v =>
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω))
          atTop (nhds 0) →
        ∃ tag : ℕ → ℝ≥0 → ℕ,
          (∀ k, ∀ v ∈ T k,
            tag k v < n k ∧ (u k) (tag k v) < v ∧
              v ≤ (u k) (tag k v + 1)) ∧
          (∀ k, ∀ v ∈ T k, ∀ z ∈ T k,
            tag k v = tag k z → v = z) ∧
          Tendsto (fun k =>
            (Finset.range (n k)).sum (fun i =>
              if i ∈ (T k).image (tag k) then 0
              else J ((u k) (i + 1)) - J ((u k) i)))
            atTop (nhds 0) := by
  classical
  filter_upwards
    [avram_p3_f_chainlimit_original_uniform_unmarked_finite_marks_envelope
      X hBV,
      avram_p3_f_chainlimit_original_raw_J_monotone X hBV]
      with ω hsource hmono
  intro J T hCover hSeparate hTail
  have hAt : ∀ k, ∃ tag : ℝ≥0 → ℕ,
      (∀ v ∈ T k,
        tag v < n k ∧ (u k) (tag v) < v ∧
          v ≤ (u k) (tag v + 1)) ∧
      (∀ v ∈ T k, ∀ z ∈ T k, tag v = tag z → v = z) ∧
      (Finset.range (n k)).sum (fun i =>
        if i ∈ (T k).image tag then 0
        else J ((u k) (i + 1)) - J ((u k) i)) ≤
        J ((u k) (n k)) - J ((u k) 0) -
          (T k).sum (fun v =>
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω) := by
    intro k
    exact hsource (u k) (n k) (T k) (hCover k) (hSeparate k)
  let tag : ℕ → ℝ≥0 → ℕ := fun k => Classical.choose (hAt k)
  have hcell : ∀ k, ∀ v ∈ T k,
      tag k v < n k ∧ (u k) (tag k v) < v ∧
        v ≤ (u k) (tag k v + 1) := by
    intro k v hv
    exact (Classical.choose_spec (hAt k)).1 v hv
  have hinj : ∀ k, ∀ v ∈ T k, ∀ z ∈ T k,
      tag k v = tag k z → v = z := by
    intro k v hv z hz heq
    exact (Classical.choose_spec (hAt k)).2.1 v hv z hz heq
  refine ⟨tag, hcell, hinj, ?_⟩
  let E : ℕ → ℝ := fun k =>
    (Finset.range (n k)).sum (fun i =>
      if i ∈ (T k).image (tag k) then 0
      else J ((u k) (i + 1)) - J ((u k) i))
  have hUpper : ∀ k, E k ≤
      J ((u k) (n k)) - J ((u k) 0) -
        (T k).sum (fun v =>
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω) := by
    intro k
    exact (Classical.choose_spec (hAt k)).2.2
  have hNonneg : ∀ k, 0 ≤ E k := by
    intro k
    dsimp only [E]
    apply Finset.sum_nonneg
    intro i hi
    by_cases hm : i ∈ (T k).image (tag k)
    · simp only [if_pos hm, le_refl]
    · simpa only [if_neg hm] using
        (sub_nonneg.mpr
          (hmono ((u k) i) ((u k) (i + 1))
            (hGrid k i (Finset.mem_range.mp hi))))
  change (fun _ : ℕ => (0 : ℝ)) ≤ E at hNonneg
  change E ≤ (fun k =>
    J ((u k) (n k)) - J ((u k) 0) -
      (T k).sum (fun v =>
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω))
    at hUpper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hTail hNonneg hUpper
