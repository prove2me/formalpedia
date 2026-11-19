-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_positive_ruincontact_full_inclusive_cash_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:58:41.653489+00:00
-- url     : https://prove2.me/submissions/5a39f1ac-5b5a-430f-92e5-123741e5dafb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_discounted_masked_contact_tail_tendsto_endpoint_atom
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_positive_ruin_endpoint_cash_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : ℝ≥0) (hτ : 0 < τ)
    (hruin : (τ : ℝ≥0∞) = ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by
  have hAtom :=
    avram_p3_grid4_original_positive_ruin_endpoint_cash_zero
      X x D ω τ hτ hruin q
  have hTail :=
    avram_p3_grid4_original_discounted_masked_contact_tail_tendsto_endpoint_atom
      X x D hD ω q hq τ τ le_rfl δ hδpos hδanti hδ
  simpa only [hAtom] using hTail
