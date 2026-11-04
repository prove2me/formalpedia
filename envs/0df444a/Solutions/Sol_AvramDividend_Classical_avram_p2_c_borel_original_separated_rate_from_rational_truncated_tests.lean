-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_rational_truncated_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:13:07.758428+00:00
-- url     : https://prove2.me/submissions/70c6a12c-6d1c-4e0d-8003-312d8ae68c93

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_dense_tests

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Rational source threshold identities identify every original separated Borel mark intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε))
    (hTests : ∀ q : ℚ,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic (q : ℝ) ∩ Iic (-ε))) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (q : ℝ) ∩ Iic (-ε)))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  have hDense : Dense (Set.range (fun q : ℚ => (q : ℝ))) :=
    Rat.denseRange_cast
  apply avram_p2_c_borel_original_separated_rate_from_dense_tests
    X s t hst ε hε B hB hBsep
    (Set.range (fun q : ℚ => (q : ℝ))) hDense
  intro a ha
  obtain ⟨q, rfl⟩ := ha
  exact hTests q
