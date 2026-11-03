-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_drift_envelope_sufficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:11:17.36881+00:00
-- url     : https://prove2.me/submissions/5dd42041-909a-433a-b455-542b089b9b16

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Explicit sufficient BV zero-cap branch: nonnegative candidate boundary
value dominates the sharp actual physical drift envelope on the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (W : ℝ) (hW : (T : ℝ) * X.drift ≤ W) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal W := by
  have hb := avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
    X hX hBV 0 (le_refl (0 : ℝ)) 0
      (by simp) D hD q hq T
  have hEnvelope :
      ENNReal.ofReal ((0 : ℝ) + (T : ℝ) * X.drift) ≤ ENNReal.ofReal W :=
    ENNReal.ofReal_le_ofReal (by simpa only [zero_add] using hW)
  exact hb.trans hEnvelope
