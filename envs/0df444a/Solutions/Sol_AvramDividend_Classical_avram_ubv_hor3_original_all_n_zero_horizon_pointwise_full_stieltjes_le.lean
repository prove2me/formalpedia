-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_all_n_zero_horizon_pointwise_full_stieltjes_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:43:40.501441+00:00
-- url     : https://prove2.me/submissions/4f7eebc8-3022-4c8d-960b-f770544a191c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_initial_right_dividend_atom_le_hjb
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (ω : Ω) :
    (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (w x) := by
  calc
    (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        (dividendMeasure D ω) ({0} : Set ℝ) :=
      avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
        D ω (min (ruinTime X x D ω) (n : ℝ≥0∞)) q
    _ ≤ ENNReal.ofReal (w x) :=
      avram_ubv_hor3_original_initial_right_dividend_atom_le_hjb
        X x q w C hw0 hw_cont hw_neg hw_smooth hw_grad hxc D hD hjump ω
