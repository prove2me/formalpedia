-- Prove2me | solution 1 for AvramDividend.Classical.avram_b175_original_genuine_marked_grid_jumpfree_plus_eventual_cutoff_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:53.684126+00:00
-- url     : https://prove2.me/submissions/bcc0ab48-609a-440e-a142-e9c13f655100

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b132_original_finite_physical_grid_negative_band_occupied_set_eventually_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A single exact finite original physical marked-grid selector simultaneously classifies all true jumpfree cells and is reached exactly by all sufficiently fine negative source cutoffs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0) :
    ∃ J : Finset ℕ,
      J ⊆ S ∧
      (∀ i ∈ S, i ∉ J → ∀ u : ℝ≥0, s i < u → u ≤ t i →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        S.filter (fun i => ∃ u : ℝ≥0, s i < u ∧ u ≤ t i ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))) = J) := by
  classical
  let J : Finset ℕ := S.filter (fun i => ∃ u : ℝ≥0,
    s i < u ∧ u ≤ t i ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
  have hJsub : J ⊆ S := Finset.filter_subset _ _
  have hNoJump : ∀ i ∈ S, i ∉ J → ∀ u : ℝ≥0, s i < u → u ≤ t i →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
    intro i hi hj u hsu hut
    by_contra hne
    exact hj (Finset.mem_filter.mpr ⟨hi, ⟨u, hsu, hut, hne⟩⟩)
  obtain ⟨N, hN⟩ :=
    avram_b132_original_finite_physical_grid_negative_band_occupied_set_eventually_exact
      X ω S s t
  refine ⟨J, hJsub, hNoJump, N, ?_⟩
  intro n hn
  simpa only [J] using hN n hn
