-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_infinite_cap_no_cap_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:13:10.094202+00:00
-- url     : https://prove2.me/submissions/6858337e-47b0-4e90-a9ef-ecd15af2a5f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under the genuine infinite-cap alternative, the original reserve
prestate can never equal the cap, so the interior is exactly positivity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤) :
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    ({p : ℝ≥0 × Ω | ENNReal.ofReal (Z p) = C} : Set (ℝ≥0 × Ω)) = ∅ ∧
    ({p : ℝ≥0 × Ω | 0 < Z p ∧ ENNReal.ofReal (Z p) < C} :
      Set (ℝ≥0 × Ω)) =
      {p : ℝ≥0 × Ω | 0 < Z p} := by
  let Z : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  constructor
  · ext p
    simp [hTop]
  · ext p
    simp [hTop]
