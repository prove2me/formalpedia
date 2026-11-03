-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_cash_witness_has_strictly_positive_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:29:47.557541+00:00
-- url     : https://prove2.me/submissions/ae69fd67-41f5-4b30-97be-8eb51ad9350b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_original_admissible_zero_start_zero_horizon_expected_cash_eq_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The positive finite-horizon complete Stieltjes cash witness is strictly
later than time zero, as shown by the exact zero-horizon atom budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ n : ℕ, 0 < n ∧ 0 <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by
  obtain ⟨n, hn⟩ :=
    avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash
      X hX hBV hFinite q hq
  have hD : IsAdmissibleLe X 0 0 (barrierStrategy X 0 0) := by
    simpa only [ENNReal.ofReal_zero] using
      (barrierStrategy_admissibleLe_nonnegative_barrier
        X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
  have hZero :=
    avram_wave7_09_original_admissible_zero_start_zero_horizon_expected_cash_eq_zero
      X 0 (barrierStrategy X 0 0) hD q
  refine ⟨n, Nat.pos_of_ne_zero ?_, hn⟩
  intro hn0
  subst n
  simp only [Nat.cast_zero] at hn
  rw [hZero] at hn
  exact (lt_irrefl _) hn
