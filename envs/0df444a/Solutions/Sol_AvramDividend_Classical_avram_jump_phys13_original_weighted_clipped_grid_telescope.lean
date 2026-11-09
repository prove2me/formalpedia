-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump_phys13_original_weighted_clipped_grid_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:16:03.724411+00:00
-- url     : https://prove2.me/submissions/e627e744-0b11-4726-8b7b-e5615d557ec9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_marked_jump_weighted_halfopen_cell_add

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The actual marked source weighted integral telescopes through every clipped final cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (e : ℕ → ℝ≥0) (he : Monotone e) (N : ℕ)
    (ρ : Ω → ℝ≥0)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    let Δ : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let J : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ I)).map
        (fun u : ℝ≥0 => (u, Δ u))
    (∫⁻ p, F p ∂J (Ioc (min (e 0) (ρ ω)) (min (e N) (ρ ω)))) =
      ∑ i ∈ Finset.range N,
        (∫⁻ p, F p ∂J
          (Ioc (min (e i) (ρ ω)) (min (e (i + 1)) (ρ ω)))) := by
  classical
  let Δ : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let J : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
    (Measure.count.restrict ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ I)).map
      (fun u : ℝ≥0 => (u, Δ u))
  let ec : ℕ → ℝ≥0 := fun i => min (e i) (ρ ω)
  have hec : Monotone ec := by
    intro i j hij
    exact min_le_min (he hij) le_rfl
  change (∫⁻ p, F p ∂J (Ioc (ec 0) (ec N))) =
    ∑ i ∈ Finset.range N, (∫⁻ p, F p ∂J (Ioc (ec i) (ec (i + 1))))
  induction N with
  | zero =>
      simp [J]
  | succ n ih =>
      have hPart :
          (∫⁻ p, F p ∂J (Ioc (ec 0) (ec (n + 1)))) =
            (∫⁻ p, F p ∂J (Ioc (ec 0) (ec n))) +
              (∫⁻ p, F p ∂J (Ioc (ec n) (ec (n + 1)))) := by
        exact AvramDividend.Classical.avram_bv_cell7_original_marked_jump_weighted_halfopen_cell_add
          X ω (ec 0) (ec n) (ec (n + 1))
          (hec (Nat.zero_le n)) (hec (Nat.le_succ n)) F hF
      simp only [Finset.sum_range_succ]
      rw [hPart, ih]
