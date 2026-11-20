-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_actual_ruincontact_caplinear_terminal_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:40:39.527592+00:00
-- url     : https://prove2.me/submissions/d0d2a480-d87b-4b80-b337-bfb4b73225ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    let V : ℝ → ℝ := fun z =>
      if ENNReal.ofReal z ≤ C then w z
      else w C.toReal + (z - C.toReal)
    let W : ℝ := if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    V W = w W := by
  let V : ℝ → ℝ := fun z =>
    if ENNReal.ofReal z ≤ C then w z
    else w C.toReal + (z - C.toReal)
  let W : ℝ := if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
    then x + X.X t ω - rightLimit D t ω
    else riskProcess X x D t ω
  by_cases h : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
  · have hc := capped_postPaymentReserve_ofReal_le_cap
      X x C D hD hxc ω t
    simp [V, W, h, hc]
  · have hc := admissibleLe_riskProcess_le_cap_all_times
      X x C D hD hxc ω t
    simp [V, W, h, hc]
