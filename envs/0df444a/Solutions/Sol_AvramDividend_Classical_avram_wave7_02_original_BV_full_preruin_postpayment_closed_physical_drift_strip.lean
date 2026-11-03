-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:43:39.217933+00:00
-- url     : https://prove2.me/submissions/4977c487-1532-4651-9d41-fdc6e819b9f7

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original BV reserve path is bounded below by solvency and above by the
actual cap and a deterministic physical-drift envelope, uniformly on the
pre-ruin clock, including the time-zero right-payment atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      0 ≤ x + X.X t ω - rightLimit D t ω ∧
      ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C ∧
      x + X.X t ω - rightLimit D t ω ≤
        x + (T : ℝ) * X.drift := by
  have hd : 0 ≤ X.drift :=
    (bv_standing_drift_pos X hX hBV).1.le
  filter_upwards
    [avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
      X hBV x D hD.1.1 T hd] with ω hUpper
  intro t ht hPre
  have hLow : 0 ≤ x + X.X t ω - rightLimit D t ω := by
    rcases hPre with hZero | hStrict
    · subst t
      exact (capped_postPaymentReserve_initial_state X x C D hD hxc ω).1
    · exact postPaymentReserve_nonnegative_strictly_before_ruin
        X x D hD.1.1 ω t hStrict
  exact ⟨hLow,
    capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t,
    hUpper t ht⟩
