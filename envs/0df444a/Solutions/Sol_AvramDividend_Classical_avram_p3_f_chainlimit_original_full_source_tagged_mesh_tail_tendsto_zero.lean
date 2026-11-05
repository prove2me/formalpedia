-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_full_source_tagged_mesh_tail_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:46:30.548012+00:00
-- url     : https://prove2.me/submissions/046e4758-ed61-4673-b96e-711ef64f48d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_unmarked_J_tail_tendsto_zero
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
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (T : ℕ → Finset ℝ≥0)
        (hCover : ∀ k, ∀ v ∈ T k, ∃ i : ℕ,
          i < n k ∧ (u k) i < v ∧ v ≤ (u k) (i + 1))
        (hSeparate : ∀ k, ∀ v ∈ T k, ∀ z ∈ T k, ∀ i : ℕ,
          i < n k → (u k) i < v → v ≤ (u k) (i + 1) →
          (u k) i < z → z ≤ (u k) (i + 1) → v = z)
        (hJTail : Tendsto (fun k =>
          J ((u k) (n k)) - J ((u k) 0) -
            (T k).sum (fun v =>
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω))
          atTop (nhds 0))
        (hYMarked : ∀ tag : ℕ → ℝ≥0 → ℕ,
          (∀ k, ∀ v ∈ T k,
            tag k v < n k ∧ (u k) (tag k v) < v ∧
              v ≤ (u k) (tag k v + 1)) →
          (∀ k, ∀ v ∈ T k, ∀ z ∈ T k,
            tag k v = tag k z → v = z) →
          Tendsto (fun k =>
            (Finset.range (n k)).sum (fun i =>
              if i ∈ (T k).image (tag k) then
                |Y ((u k) (i + 1)) - Y ((u k) i)|
              else 0)) atTop (nhds 0)),
        ∃ tag : ℕ → ℝ≥0 → ℕ,
          (∀ k, ∀ v ∈ T k,
            tag k v < n k ∧ (u k) (tag k v) < v ∧
              v ≤ (u k) (tag k v + 1)) ∧
          (∀ k, ∀ v ∈ T k, ∀ z ∈ T k,
            tag k v = tag k z → v = z) ∧
          Tendsto (fun k =>
            (Finset.range (n k)).sum (fun i =>
              if i ∈ (T k).image (tag k) then
                |Y ((u k) (i + 1)) - Y ((u k) i)|
              else
                |J ((u k) (i + 1)) - J ((u k) i)|))
            atTop (nhds 0) := by
  classical
  filter_upwards
    [avram_p3_f_chainlimit_original_uniform_unmarked_J_tail_tendsto_zero
      X hBV u n hGrid,
     avram_p3_f_chainlimit_original_raw_J_monotone X hBV]
      with ω hUnmarked hMono
  intro J Y T hCover hSeparate hJTail hYMarked
  obtain ⟨tag, hCell, hInj, hJ⟩ :=
    hUnmarked T hCover hSeparate hJTail
  refine ⟨tag, hCell, hInj, ?_⟩
  have hY := hYMarked tag hCell hInj
  let Mark : ℕ → ℝ := fun k =>
    (Finset.range (n k)).sum (fun i =>
      if i ∈ (T k).image (tag k) then
        |Y ((u k) (i + 1)) - Y ((u k) i)|
      else 0)
  let Jump : ℕ → ℝ := fun k =>
    (Finset.range (n k)).sum (fun i =>
      if i ∈ (T k).image (tag k) then 0
      else J ((u k) (i + 1)) - J ((u k) i))
  have hEq : ∀ k,
      (Finset.range (n k)).sum (fun i =>
        if i ∈ (T k).image (tag k) then
          |Y ((u k) (i + 1)) - Y ((u k) i)|
        else |J ((u k) (i + 1)) - J ((u k) i)|) =
      Mark k + Jump k := by
    intro k
    change (Finset.range (n k)).sum (fun i =>
        if i ∈ (T k).image (tag k) then
          |Y ((u k) (i + 1)) - Y ((u k) i)|
        else |J ((u k) (i + 1)) - J ((u k) i)|) =
      (Finset.range (n k)).sum (fun i =>
        if i ∈ (T k).image (tag k) then
          |Y ((u k) (i + 1)) - Y ((u k) i)| else 0) +
      (Finset.range (n k)).sum (fun i =>
        if i ∈ (T k).image (tag k) then 0
        else J ((u k) (i + 1)) - J ((u k) i))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hm : i ∈ (T k).image (tag k)
    · simp [hm]
    · have hj : 0 ≤ J ((u k) (i + 1)) - J ((u k) i) :=
        sub_nonneg.mpr (hMono ((u k) i) ((u k) (i + 1))
          (hGrid k i (Finset.mem_range.mp hi)))
      simp [hm, abs_of_nonneg hj]
  have hSum : Tendsto (fun k => Mark k + Jump k)
      atTop (nhds (0 : ℝ)) := by
    simpa only [zero_add] using hY.add hJ
  simpa only [hEq] using hSum
