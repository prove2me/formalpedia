-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top12_original_zero_nu_positive_ruin_prepayment_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T14:00:36.028209+00:00
-- url     : https://prove2.me/submissions/07b96160-695f-4307-86d9-dffbbb56527e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_all_positive_clock_preright_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn12_ruin_endpoint_payment_inter_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At a positive random ruin clock, terminal contact is pre-right payment
    and the strict cash measure excludes the ruin right-jump atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (t : ℝ≥0∞) = ruinTime X x D ω →
      Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
        riskProcess X x D t ω ∧
      ∀ a : ℝ,
        paymentTimes (ruinTime X x D ω) ∩ Ioc a (t : ℝ) =
          paymentTimes (ruinTime X x D ω) ∩ Ioo a (t : ℝ) := by
  filter_upwards [avram_ubv_top12_original_zero_nu_all_positive_clock_preright_leftlim X hν D hD x] with ω hLeft
  intro t ht hRuin
  constructor
  · calc
      Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
        Function.leftLim (fun s : ℝ≥0 => riskProcess X x D s ω) t :=
          (avram_wave4_p2_original_prepost_reserve_same_leftlim X x D hD ω t ht).symm
      _ = riskProcess X x D t ω := hLeft t ht
  · intro a
    have hb : 0 < (t : ℝ) := by exact_mod_cast ht
    have hσ : ENNReal.ofReal (t : ℝ) = ruinTime X x D ω := by
      simpa using hRuin
    exact avram_p3_grid4_turn12_ruin_endpoint_payment_inter_eq
      (ruinTime X x D ω) (t : ℝ) hb hσ a
