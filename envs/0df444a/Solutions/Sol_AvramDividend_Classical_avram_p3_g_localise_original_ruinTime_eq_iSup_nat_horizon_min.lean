-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_ruinTime_eq_iSup_nat_horizon_min
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:42:16.54062+00:00
-- url     : https://prove2.me/submissions/0f20eea0-e88b-4ef6-a2a9-45f06ac11206

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original ENNReal ruin clock is the supremum of
finite natural-horizon truncations, including infinite ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ ω : Ω,
      (⨆ n : ℕ, min (ruinTime X x D ω) (n : ℝ≥0∞)) =
        ruinTime X x D ω := by
  intro ω
  apply le_antisymm
  · exact iSup_le fun n => min_le_left _ _
  · by_cases hFinite : ruinTime X x D ω = ⊤
    · simpa [hFinite] using
        (show (⨆ n : ℕ, (n : ℝ≥0∞)) = ⊤ from ENNReal.iSup_natCast).ge
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hFinite
      have hMin :
          min (ruinTime X x D ω) (n : ℝ≥0∞) =
            ruinTime X x D ω := min_eq_left hn.le
      calc
        ruinTime X x D ω =
            min (ruinTime X x D ω) (n : ℝ≥0∞) := hMin.symm
        _ ≤ (⨆ k : ℕ, min (ruinTime X x D ω) (k : ℝ≥0∞)) :=
          le_iSup_of_le n le_rfl
