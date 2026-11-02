-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_actual_original_measurable_jump_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:02:27.224144+00:00
-- url     : https://prove2.me/submissions/dd704b44-2ec1-4980-bd78-a2af9990e3d2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_rational_grid_actual_jump_coverage
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_first_candidate_filter_covers_original_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ (T : ℕ → Ω → ℝ≥0) (A : ℕ → Set Ω),
      (∀ n, Measurable (T n)) ∧ (∀ n, MeasurableSet (A n)) ∧
      (∀ ω n, ω ∈ A n → 0 < T n ω ∧
        X.X (T n ω) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω) ≠ 0) ∧
      (∀ ω n m, ω ∈ A n → ω ∈ A m → T n ω = T m ω → n = m) ∧
      (∀ ω u, 0 < u →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
        ∃ n, ω ∈ A n ∧ T n ω = u) := by
  classical
  obtain ⟨D, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hnonempty : D.Nonempty := hdense.nonempty
  obtain ⟨grid, hgrid⟩ := hcount.exists_eq_range hnonempty
  have hdenseGrid : DenseRange grid := by
    change Dense (Set.range grid)
    rw [← hgrid]
    exact hdense
  obtain ⟨pairs, hpairs⟩ := exists_surjective_nat (ℕ × ℚ)
  let T : ℕ → Ω → ℝ≥0 := fun k ω =>
    (⨅ n : ℕ, {ω : Ω | grid (pairs k).1 < grid n ∧
        X.X (grid n) ω < ((pairs k).2 : ℝ)}.piecewise
      (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) ω).toNNReal
  have hTC := avram_wave5_02a_rational_grid_actual_jump_coverage
    X grid hdenseGrid pairs hpairs
  have hT : ∀ n, Measurable (T n) := hTC.1
  have hCover := hTC.2
  let A : ℕ → Set Ω := fun n => {ω |
    0 < T n ω ∧
    X.X (T n ω) ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω) ≠ 0 ∧
    ∀ m < n, T m ω ≠ T n ω}
  have hFilter := avram_wave5_02a_actual_jump_candidates_measurable_dedup X T hT
  have hCoverActive := (avram_wave5_02a_first_candidate_filter_covers_original_jumps
    X T hT hCover).2
  refine ⟨T, A, hT, hFilter.1, ?_, ?_, hCoverActive⟩
  · intro ω n hn
    exact ⟨hn.1, hn.2.1⟩
  · intro ω n m hn hm heq
    by_contra hne
    exact hFilter.2 ω n m hn hm hne heq
