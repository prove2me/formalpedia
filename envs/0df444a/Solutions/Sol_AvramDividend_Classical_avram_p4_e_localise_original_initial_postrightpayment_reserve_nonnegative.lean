-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_initial_postrightpayment_reserve_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:47:02.324932+00:00
-- url     : https://prove2.me/submissions/78a597ed-ee06-48c8-881d-3b02ef9a1cf1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact initial right dividend is affordable from the source initial book reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (ω : Ω) :
    0 ≤ x + X.X 0 ω - rightLimit D 0 ω := by
  have hPay := hD.2 ω 0 (Or.inl rfl)
  dsimp [riskProcess] at hPay
  linarith
