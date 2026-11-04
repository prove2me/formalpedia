-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_rational_below_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:36:23.271807+00:00
-- url     : https://prove2.me/submissions/02200a9b-49f0-413b-bf44-0b3ba01d3170

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_below_cutoff_tests

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original separated rate from rational halfline tests below a cutoff and one cutoff mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε))
    (hCut : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (-ε))))
    (hBelow : ∀ q : ℚ, (q : ℝ) < -ε →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (q : ℝ)) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (q : ℝ)))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  have hDense : Dense (Set.range (fun q : ℚ => (q : ℝ))) :=
    Rat.denseRange_cast
  apply avram_p2_c_borel_original_separated_rate_from_below_cutoff_tests
    X s t hst ε hε B hB hBsep
    (Set.range (fun q : ℚ => (q : ℝ))) hDense hCut
  intro a ha hac
  obtain ⟨q, rfl⟩ := ha
  exact hBelow q hac
