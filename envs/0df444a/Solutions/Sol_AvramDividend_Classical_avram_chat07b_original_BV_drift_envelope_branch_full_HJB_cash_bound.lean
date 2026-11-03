-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07b_original_BV_drift_envelope_branch_full_HJB_cash_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:15:05.593115+00:00
-- url     : https://prove2.me/submissions/413e750d-2762-4228-bd30-e1d93897d348

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
noncomputable section

/-- The original BV source drift envelope closes the full HJB cash estimate
on its exact deterministic-horizon domination branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (w : ℝ → ℝ)
    (hEnvelope : x + (T : ℝ) * X.drift ≤ w x) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ⊓ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  calc
    _ ≤ ENNReal.ofReal (x + (T : ℝ) * X.drift) :=
      avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
        X hX hBV x hx C hxc D hD q hq T
    _ ≤ ENNReal.ofReal (w x) :=
      ENNReal.ofReal_le_ofReal hEnvelope
