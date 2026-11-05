-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_stopped_strict_interior_finite_rational_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:50:59.822082+00:00
-- url     : https://prove2.me/submissions/ceb7d83d-4bde-481a-ac54-0eddb70bd0ab

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_stopped_strict_interior_countable_rational_band_union

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact exhaustion of the original stopped strict interior by
deterministic finite sets of rational compact-substrip events. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    ({p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < Z p ∧ ENNReal.ofReal (Z p) < C} : Set (ℝ≥0 × Ω)) =
      ⋃ S : Finset (ℚ × ℚ), ⋃ ab ∈ S,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          0 < (ab.1 : ℝ) ∧ (ab.1 : ℝ) ≤ 2 ∧
          (ab.1 : ℝ) ≤ (ab.2 : ℝ) ∧
          Icc ((ab.1 : ℝ) / 2) (ab.2 : ℝ) ⊆
            {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} ∧
          Z p ∈ Ioo (ab.1 : ℝ) (ab.2 : ℝ)} := by
  classical
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let Z : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  have hCover :=
    avram_p3_g_localise_original_stopped_strict_interior_countable_rational_band_union
      X x C D hD T
  change
    ({p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      0 < Z p ∧ ENNReal.ofReal (Z p) < C} : Set (ℝ≥0 × Ω)) =
    ⋃ a : ℚ, ⋃ b : ℚ,
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < (a : ℝ) ∧ (a : ℝ) ≤ 2 ∧ (a : ℝ) ≤ (b : ℝ) ∧
        Icc ((a : ℝ) / 2) (b : ℝ) ⊆
          {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} ∧
        Z p ∈ Ioo (a : ℝ) (b : ℝ)} at hCover
  change
    ({p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      0 < Z p ∧ ENNReal.ofReal (Z p) < C} : Set (ℝ≥0 × Ω)) =
      ⋃ S : Finset (ℚ × ℚ), ⋃ ab ∈ S,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          0 < (ab.1 : ℝ) ∧ (ab.1 : ℝ) ≤ 2 ∧
          (ab.1 : ℝ) ≤ (ab.2 : ℝ) ∧
          Icc ((ab.1 : ℝ) / 2) (ab.2 : ℝ) ⊆
            {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} ∧
          Z p ∈ Ioo (ab.1 : ℝ) (ab.2 : ℝ)}
  rw [hCover]
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨{(a, b)}, (a, b), by simp, h⟩
  · rintro ⟨S, ⟨a, b⟩, _hS, h⟩
    exact ⟨a, b, h⟩
