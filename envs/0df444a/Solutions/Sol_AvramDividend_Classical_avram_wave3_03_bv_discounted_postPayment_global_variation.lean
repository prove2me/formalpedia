-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_global_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:57:58.693637+00:00
-- url     : https://prove2.me/submissions/27f92872-359e-4dc2-b2b1-5269d8bf1ef4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_global_Lipschitz_localisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuinely discounted source post-payment HJB test has global
    bounded variation at every frozen finite horizon, after exact
    compact-band Lipschitz extension. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (lo hi : ℝ) (L : NNReal)
    (hw : LipschitzOnWith L w (Icc lo hi)) :
    ∃ v : ℝ → ℝ,
      LipschitzWith L v ∧ Set.EqOn w v (Icc lo hi) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        BoundedVariationOn
          (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) *
            v (x + X.X (min t T) ω - rightLimit D (min t T) ω))
          Set.univ := by
  obtain ⟨v, hvL, hvEq, hvpaths⟩ :=
    avram_wave3_03_bv_postPayment_global_Lipschitz_localisation
      X hX hBV x D hD w lo hi L hw
  refine ⟨v, hvL, hvEq, ?_⟩
  filter_upwards [hvpaths] with ω hω
  intro T
  exact (avram_wave3_03_bv_discount_exp_global_variation q hq).fun_mul (hω T)
