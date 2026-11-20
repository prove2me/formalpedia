-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_uniform_clipped_negative_mark_total_cell_count_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:28:12.851031+00:00
-- url     : https://prove2.me/submissions/ef626814-09e8-4115-b6b5-b5a17a32363a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_trueclock_clipped_marked_grid_telescoping
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : Ω → ℝ≥0) (n m : ℕ)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (δ : ℝ) (hδ : 0 < δ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    (∑ i ∈ Finset.range (m + 1),
      NX (Ioc (u i) (u (i+1)) ×ˢ
        {z : ℝ | δ ≤ dist z 0})) < ⊤ := by
  classical
  have hB : MeasurableSet {z : ℝ | δ ≤ dist z 0} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  have htel :=
    avram_pj_workerC_trueclock_clipped_marked_grid_telescoping
      X ω ρ n m hρbound {z : ℝ | δ ≤ dist z 0} hB
  dsimp only at htel ⊢
  rw [htel]
  exact avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path
    X ω (ρ ω) δ hδ
