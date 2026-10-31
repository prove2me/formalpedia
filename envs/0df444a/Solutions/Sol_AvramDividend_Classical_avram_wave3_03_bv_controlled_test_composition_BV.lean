-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_controlled_test_composition_BV
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:50:58.623902+00:00
-- url     : https://prove2.me/submissions/64efc623-7826-4611-9e99-6c596ce04bb1

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Along every bounded-variation original controlled Levy sample path,
a test value function that is Lipschitz on the attained reserve band has
bounded variation on each localised time set. No atom or diffusion-only
approximation is imposed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (lo hi : ℝ) (L : NNReal)
    (hw : LipschitzOnWith L w (Icc lo hi)) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (s : Set ℝ≥0),
      s ⊆ Icc (0 : ℝ≥0) T →
      Set.MapsTo (fun t => riskProcess X x D t ω) s (Icc lo hi) →
      BoundedVariationOn
        (fun t => w (riskProcess X x D t ω)) s := by
  filter_upwards [avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact
    X hX hBV x D hD] with ω hω
  intro T s hs hmaps
  have hbase : BoundedVariationOn
      (fun t : ℝ≥0 => riskProcess X x D t ω) s :=
    (hω T).mono hs
  simpa only [Function.comp_def] using
    hw.comp_boundedVariationOn hmaps hbase
