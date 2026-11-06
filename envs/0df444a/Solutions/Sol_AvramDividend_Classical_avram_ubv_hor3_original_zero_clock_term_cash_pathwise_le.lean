-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:15:57.88932+00:00
-- url     : https://prove2.me/submissions/dc1719f6-672f-484b-bc63-05dabe1f0c6f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_zero_clock_rightpayment_term_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (ω : Ω) (hZero : τ ω = 0) :
    Term ω + Cash ω ≤ w x := by
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hAtom :=
    avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
      X x q D hStrategy τ Cash hCash ω hZero
  have hD0 : D 0 ω = 0 := hStrategy.1 ω
  have hD0nonneg : 0 ≤ D 0 ω := by simp [hD0]
  have hRightNonneg : 0 ≤ rightLimit D 0 ω :=
    le_trans hD0nonneg
      (dividendStrategy_le_rightLimit D hStrategy ω 0)
  have hCashZero : Cash ω = rightLimit D 0 ω := by
    rw [hAtom, hD0, sub_zero, ENNReal.toReal_ofReal hRightNonneg]
  have hTermZero :=
    (avram_p4_e_localise_original_zero_clock_rightpayment_term_exact
      X x D τ W Term q w hW hTerm ω hZero).2
  have hLedger :=
    avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
      X w x C D hD hjump ω
  rw [hTermZero, hCashZero]
  exact hLedger
