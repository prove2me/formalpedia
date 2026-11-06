-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn15_original_contact_cell_closed_minus_strict_real_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:27:07.108708+00:00
-- url     : https://prove2.me/submissions/94741953-61f7-41ce-a770-5484bb0f6581

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn14_original_closed_contact_tail_real_endpoint_automatic
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn11_original_masked_strict_contact_cash_toReal_zero
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
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T τ : ℝ≥0) (hτT : τ ≤ T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal -
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal)
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        ({(τ : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) := by
  have hClosed :=
    avram_bv_env3_turn14_original_closed_contact_tail_real_endpoint_automatic
      X x D hD ω q hq T τ hτT δ hδpos hδanti hδ
  have hStrict :=
    avram_bv_env3_turn11_original_masked_strict_contact_cash_toReal_zero
      X x D hD ω q hq T τ hτT δ hδpos hδanti hδ
  simpa only [sub_zero] using hClosed.sub hStrict
