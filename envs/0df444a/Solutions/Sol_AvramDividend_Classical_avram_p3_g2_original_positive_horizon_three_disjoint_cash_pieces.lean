-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_positive_horizon_three_disjoint_cash_pieces
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:39:38.682791+00:00
-- url     : https://prove2.me/submissions/91067828-ff63-496c-bff3-8162c448af3a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Literal positive-horizon stopped Stieltjes Cash partitions into the
already-paid time-zero right atom, an interior open interval and exactly
one strict-survival right-horizon atom. At ruin at S the last term is zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) (hS : 0 < S) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    rightLimit D 0 ω +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo (0 : ℝ) (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * (rightLimit D S ω - D S ω)
       else 0) := by
  rw [avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
    X x C D hD ω q hq S]
  rw [avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
    X x C D hD w hjump ω q hq S hS]
  simp [ne_of_gt hS]
