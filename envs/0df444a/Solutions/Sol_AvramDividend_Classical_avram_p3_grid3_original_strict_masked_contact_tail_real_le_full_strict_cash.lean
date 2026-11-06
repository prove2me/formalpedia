-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_strict_masked_contact_tail_real_le_full_strict_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:02:03.361475+00:00
-- url     : https://prove2.me/submissions/8f91767c-b36c-471d-8be6-df326945a212

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The strictly left-masked original contact cash cannot exceed full strict-horizon cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T τ : ℝ≥0) (hτT : τ ≤ T) (δ : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo ((τ : ℝ) - δ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal := by
  have hτReal : (τ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hτT
  have hsub :
      paymentTimes (ruinTime X x D ω) ∩
        Ioo ((τ : ℝ) - δ) (τ : ℝ) ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ) := by
    intro t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2.2 hτReal⟩
  have hfin :=
    avram_limit2_original_strict_discounted_cash_finite_all_paths
      X q hq x D hD ω (T : ℝ) (by positivity)
  exact ENNReal.toReal_mono hfin (lintegral_mono_set hsub)
