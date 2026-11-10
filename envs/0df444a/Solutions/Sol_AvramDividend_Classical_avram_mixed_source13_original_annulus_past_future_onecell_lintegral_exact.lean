-- Prove2me | solution 1 for AvramDividend.Classical.avram_mixed_source13_original_annulus_past_future_onecell_lintegral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:12:22.639871+00:00
-- url     : https://prove2.me/submissions/dbaf900b-ef2c-46e2-a46b-1f74606b37fa

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_offtime_lintegral_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Reuse the source-exact physical annulus past/future lintegral bridge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) (hnm : n ≤ m) :
    let c : ℝ := -(1 / ((n : ℝ) + 1))
    let d : ℝ := -(1 / ((m : ℝ) + 1))
    let B : Set ℝ := Ioc c d
    let J : ℝ≥0 → ℝ≥0 → Set ℝ → Ω → ℝ≥0∞ := fun a b C ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ C)
    (∫⁻ ω, J 0 s B ω * J s t B ω ∂P) =
      ((s : ℝ≥0∞) * X.ν B) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  letI : IsProbabilityMeasure P := X.isProbability
  simpa only using
    (avram_mix_fin_source13_original_annulus_offtime_lintegral_bridge
      X s t hst n m hnm)
