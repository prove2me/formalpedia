-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger117_original_initial_contact_plus_dividend_atom_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:32:14.859342+00:00
-- url     : https://prove2.me/submissions/131fba66-3f3d-41c6-bf93-5ed4e2132907

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual time-zero Stieltjes dividend atom is paid by the initial reward drop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (hD0 : D 0 ω = 0) (hRight : 0 ≤ rightLimit D 0 ω) :
    (w (x - rightLimit D 0 ω) - w x) +
      (dividendMeasure D ω ({0} : Set ℝ)).toReal ≤ 0 := by
  have hbudget := avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
    X w x C D hD hjump ω
  have hmeasure0 : dividendMeasure D ω ({0} : Set ℝ) =
      ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) := by
    simpa using dividendMeasure_singleton_eq_rightLimit_sub
      D hD.1.1 ω 0
  rw [hmeasure0, hD0, sub_zero, ENNReal.toReal_ofReal hRight]
  linarith
