-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_strict_interior_eq_countable_rational_band_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:20:59.879863+00:00
-- url     : https://prove2.me/submissions/6ca46088-100a-42bf-83ac-75ec407c2dbb

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

/-- The literal original pre-reserve strict interior is exactly a countable
union of rational interior bands with compact C1 enlargement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞) :
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    ({p : ℝ≥0 × Ω | 0 < Z p ∧ ENNReal.ofReal (Z p) < C} :
       Set (ℝ≥0 × Ω)) =
      ⋃ a : ℚ, ⋃ b : ℚ,
        {p : ℝ≥0 × Ω |
          0 < (a : ℝ) ∧ (a : ℝ) ≤ 2 ∧
          (a : ℝ) ≤ (b : ℝ) ∧
          Icc ((a : ℝ) / 2) (b : ℝ) ⊆
            {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} ∧
          Z p ∈ Ioo (a : ℝ) (b : ℝ)} := by
  let Z : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hPos, hCap⟩
    obtain ⟨a, b, ha, ha2, hab, hyIoo, hBand⟩ :=
      avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover
        C (Z p) hPos hCap
    exact ⟨a, b, ha, ha2, hab, hBand, hyIoo⟩
  · rintro ⟨a, b, ha, _ha2, _hab, hBand, hyIoo⟩
    have hLower : (a : ℝ) / 2 ≤ Z p := by
      linarith [hyIoo.1]
    exact hBand ⟨hLower, le_of_lt hyIoo.2⟩
