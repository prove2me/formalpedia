-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_random_pre_ruin_full_cash_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:37:36.686807+00:00
-- url     : https://prove2.me/submissions/02eaf02b-1c42-4655-950a-0c83d09f6b2a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_paymentTimes_discounted_cell_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original random strictly pre-ruin cash, initial atom, and frozen source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (ω : Ω)
    (hPre : (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D 0 ω +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (0 : ℝ) (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) - w x ≤
      V (x + X.X (τ ω) ω - rightLimit D 0 ω) -
        V (x - rightLimit D 0 ω) := by
  have hCell :=
    avram_p3_c_bvchain_public_original_paymentTimes_discounted_cell_nonpos
      X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      D hD ω q hq 0 (τ ω) zero_le hPre
  simp only [NNReal.coe_zero, mul_zero, neg_zero,
    Real.exp_zero, one_mul] at hCell
  have hT := (avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
    X x C hC hxc w V hVtop hVfinite D hD ω (τ ω)).2
  have hZero := (avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
    X x C hC hxc w V hVtop hVfinite D hD ω 0).2
  have hInitial := avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
    X w x C D hD hjump ω
  rw [hT] at hCell
  simp only [X.X_zero, add_zero] at hZero
  rw [hZero]
  linarith only [hCell, hInitial]
