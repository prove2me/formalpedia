-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_route11_zero_cap_contact_positive_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T08:30:21.174358+00:00
-- url     : https://prove2.me/submissions/62dfc9b9-6449-4eb7-bd37-6b75368f4a17

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample
import Theorems.Thm_AvramDividend_Classical_zero_cap_rightLimit_zero_at_origin
import Theorems.Thm_AvramDividend_Classical_zero_cap_no_right_dividend_jump_before_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact zero-cap BV contact and positive Stieltjes cash obstruction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ n : ℕ,
      IsAdmissibleLe X 0 0 (barrierStrategy X 0 0) ∧
      (∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 (barrierStrategy X 0 0) ω) →
        rightLimit (barrierStrategy X 0 0) t ω =
          barrierStrategy X 0 0 t ω) ∧
      0 < (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by
  classical
  obtain ⟨hD, n, hn, hbad⟩ :=
    avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample
      X hX hBV hFinite q hq
  refine ⟨n, hD, ?_, ?_⟩
  · intro ω t ht
    by_cases hz : t = 0
    · subst t
      have hD0 : (barrierStrategy X 0 0) 0 ω = 0 := hD.1.1.1 ω
      have hR0 :=
        zero_cap_rightLimit_zero_at_origin
          X (barrierStrategy X 0 0) hD ω
      simpa [hD0] using hR0
    · have htpos : 0 < t := pos_iff_ne_zero.mpr hz
      exact zero_cap_no_right_dividend_jump_before_ruin
        X (barrierStrategy X 0 0) hD ω t htpos (ht.resolve_left hz)
  · simpa using (not_le.mp hbad)
