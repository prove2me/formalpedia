-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_all_admissible_full_value_iff_sharp_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:43:43.546616+00:00
-- url     : https://prove2.me/submissions/5cdee8a6-e68d-4afc-b023-dbf36f3e3610

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_admissible_dividendValue_le_barrier_at_zero
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_first_jump_payout
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact all-strategy infinite-horizon original BV cap-zero dividend
value allowance. The full Lévy source and Stieltjes reward are unchanged. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (A : ℝ≥0∞) :
    (∀ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D →
      dividendValue X q 0 D ≤ A) ↔
    ENNReal.ofReal
      (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) ≤ A := by
  have hExact :
      dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal
        (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) := by
    rw [barrierValue_self_eq_barrierSupValue,
      bv_finite_activity_zero_reflected_first_jump_payout
        X hX q hq hBV hFinite]
  constructor
  · intro hAll
    have hBarrier : IsAdmissibleLe X 0 (0 : ℝ≥0∞)
        (barrierStrategy X 0 0) := by
      simpa only [ENNReal.ofReal_zero] using
        (barrierStrategy_admissibleLe_nonnegative_barrier
          X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
    have hLe := hAll (barrierStrategy X 0 0) hBarrier
    rw [hExact] at hLe
    exact hLe
  · intro hThreshold D hD
    have hLe :=
      zero_cap_admissible_dividendValue_le_barrier_at_zero
        X hX q hq D hD
    rw [hExact] at hLe
    exact hLe.trans hThreshold
