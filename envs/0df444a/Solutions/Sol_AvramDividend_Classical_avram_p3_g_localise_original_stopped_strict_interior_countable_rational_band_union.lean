-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_stopped_strict_interior_countable_rational_band_union
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:27:44.612052+00:00
-- url     : https://prove2.me/submissions/e682982f-b700-475b-b114-5786d5fbc91d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine stopped strict-cap interior equals the countable union
of original pre-reserve open rational C1-band regions. -/
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
      ⋃ a : ℚ, ⋃ b : ℚ,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          0 < (a : ℝ) ∧ (a : ℝ) ≤ 2 ∧ (a : ℝ) ≤ (b : ℝ) ∧
          Icc ((a : ℝ) / 2) (b : ℝ) ⊆
            {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} ∧
          Z p ∈ Ioo (a : ℝ) (b : ℝ)} := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let Z : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hStop, hPos, hCap⟩
    obtain ⟨a, b, ha, ha2, hab, hyIoo, hBand⟩ :=
      avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover
        C (Z p) hPos hCap
    exact ⟨a, b, hStop, ha, ha2, hab, hBand, hyIoo⟩
  · rintro ⟨a, b, hStop, ha, _ha2, _hab, hBand, hyIoo⟩
    have hLower : (a : ℝ) / 2 ≤ Z p := by
      linarith [hyIoo.1]
    exact ⟨hStop, hBand ⟨hLower, le_of_lt hyIoo.2⟩⟩
