-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_postPayment_weighted_test_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:40:08.012068+00:00
-- url     : https://prove2.me/submissions/4fea7823-d3e2-4751-b216-da2d072dd866

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_test_composition_BV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A BV time discount preserves the pathwise variation of a locally
    Lipschitz test of the genuine post-payment controlled BV reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (lo hi : ℝ) (L : NNReal)
    (hw : LipschitzOnWith L w (Icc lo hi))
    (d : ℝ≥0 → ℝ)
    (hd : ∀ T : ℝ≥0, BoundedVariationOn d (Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (s : Set ℝ≥0),
      s ⊆ Icc (0 : ℝ≥0) T →
      Set.MapsTo (fun t => x + X.X t ω - rightLimit D t ω) s (Icc lo hi) →
      BoundedVariationOn
        (fun t => d t * w (x + X.X t ω - rightLimit D t ω)) s := by
  filter_upwards [avram_wave3_03_bv_postPayment_test_composition_BV
    X hX hBV x D hD w lo hi L hw] with ω hω
  intro T s hs hmaps
  have htime : BoundedVariationOn d s := (hd T).mono hs
  exact htime.fun_mul (hω T s hs hmaps)
