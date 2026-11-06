-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn14_original_closed_contact_tail_real_endpoint_automatic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:22:58.700212+00:00
-- url     : https://prove2.me/submissions/a6efb74c-6309-496f-829c-b4cd9020d714

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_closed_contact_tail_toReal_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn13_original_finite_discounted_stopped_endpoint_atom
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
          ∂(dividendMeasure D ω)).toReal)
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        ({(τ : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) := by
  have hFinite :=
    avram_bv_env3_turn13_original_finite_discounted_stopped_endpoint_atom
      D hD ω (ruinTime X x D ω) τ T hτT q hq
  exact avram_bv_env3_turn12_original_closed_contact_tail_toReal_endpoint
    X x D hD ω q hq T τ hτT δ hδpos hδanti hδ (ne_of_lt hFinite)
