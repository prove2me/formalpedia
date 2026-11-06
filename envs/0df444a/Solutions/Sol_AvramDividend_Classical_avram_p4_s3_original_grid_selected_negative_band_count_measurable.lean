-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_grid_selected_negative_band_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:49:09.432825+00:00
-- url     : https://prove2.me/submissions/b29f07f1-bf7d-4c20-85c0-1e2876ec1887

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_ncard_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A measurable grid selector preserves measurability of the true original
negative-band jump count, using only fixed-time count measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (tick : Ω → ℕ) (htick : Measurable tick)
    (grid : ℕ → ℝ≥0) :
    Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard) := by
  let K : ℝ≥0 → Ω → ℕ := fun T ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  have hfixed (T : ℝ≥0) : Measurable (K T) :=
    avram_p4_f2_original_negative_band_ncard_measurable X T n
  change Measurable (fun ω => K (grid (tick ω)) ω)
  intro s hs
  have hpre : (fun ω => K (grid (tick ω)) ω) ⁻¹' s =
      ⋃ k : ℕ, {ω : Ω | tick ω = k} ∩ (K (grid k)) ⁻¹' s := by
    ext ω
    constructor
    · intro hw
      apply Set.mem_iUnion.mpr
      refine ⟨tick ω, ?_⟩
      exact ⟨rfl, hw⟩
    · intro hw
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
      obtain ⟨ht, hv⟩ := hk
      change K (grid (tick ω)) ω ∈ s
      rw [ht]
      exact hv
  rw [hpre]
  exact MeasurableSet.iUnion (fun k =>
    (htick (measurableSet_singleton k)).inter ((hfixed (grid k)) hs))
