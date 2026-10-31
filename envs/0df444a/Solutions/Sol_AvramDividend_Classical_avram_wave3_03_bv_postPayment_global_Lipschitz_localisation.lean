-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_postPayment_global_Lipschitz_localisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:45:04.154996+00:00
-- url     : https://prove2.me/submissions/464a745c-c8bf-40e6-b490-1a742b7928cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every locally Lipschitz HJB test on a compact reserve band admits
    a globally Lipschitz representative whose value on the true stopped
    post-payment BV reserve has global variation at finite horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (lo hi : ℝ) (L : NNReal)
    (hw : LipschitzOnWith L w (Icc lo hi)) :
    ∃ v : ℝ → ℝ,
      LipschitzWith L v ∧ Set.EqOn w v (Icc lo hi) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        BoundedVariationOn
          (fun t : ℝ≥0 => v
            (x + X.X (min t T) ω - rightLimit D (min t T) ω))
          Set.univ := by
  obtain ⟨v, hvLip, hvEq⟩ := hw.extend_real
  refine ⟨v, hvLip, hvEq, ?_⟩
  filter_upwards [
    avram_wave3_03_bv_postPayment_truncated_global_variation X hX hBV x D hD
  ] with ω hω
  intro T
  simpa only [Function.comp_def] using
    hvLip.comp_boundedVariationOn (hω T)
