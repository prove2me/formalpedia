-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_topcap_zero_or_strict_payment_residual_cash_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:03:54.59116+00:00
-- url     : https://prove2.me/submissions/e1e09287-f9ef-4058-a762-2fa558f54a36

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_strict_source_payment_residual_cash_epsilon
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_canonical_caplinear_cash_epsilon
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_payment_residual_signed_sum_rearrange
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_each_grid_caplinear_signed_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ η (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D s η - D s η ≤
        w (riskProcess X x D s η) -
        w (riskProcess X x D s η - (rightLimit D s η - D s η)))
    (ω : Ω) (t : ℝ≥0)
    (hClock : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (ht : t ≤ (n : ℝ≥0)) :
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let Cash : ℝ≥0∞ :=
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop,
      Cash.toReal + (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (m j),
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
          (w (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω) -
            w (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω)))
      ≤ ε := by
  dsimp only
  rcases hClock with hZero | hStrict
  . subst t
    let tau : Ω → ℝ≥0 := fun _ => 0
    let CashFun : Ω → ℝ := fun η =>
      (∫⁻ r in paymentTimes (ruinTime X x D η) ∩ Iic (tau η : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D η)).toReal
    have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
    have hCashIdentity : ∀ η, CashFun η =
        (∫⁻ r in paymentTimes (ruinTime X x D η) ∩ Iic (tau η : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D η)).toReal :=
      fun _ => rfl
    have hc0 := avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
      X x q D hStrat tau CashFun hCashIdentity ω rfl
    have hd0 : D 0 ω = 0 := hStrat.1 ω
    have hRightNonneg : 0 ≤ rightLimit D 0 ω :=
      by simpa [hd0] using (dividendStrategy_le_rightLimit D hStrat ω 0)
    have hCashEq : CashFun ω = rightLimit D 0 ω := by
      simpa [hd0, ENNReal.toReal_ofReal hRightNonneg] using hc0
    have hInit := avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
      X w x C D hD hjump ω
    intro ε hε
    apply Filter.Eventually.of_forall
    intro j
    have hBound : CashFun ω +
        (w (x - rightLimit D 0 ω) - w x) ≤ 0 := by
      rw [hCashEq]
      linarith
    have hEps : CashFun ω +
        (w (x - rightLimit D 0 ω) - w x) ≤ ε :=
      le_trans hBound (le_of_lt hε)
    simpa [CashFun, tau] using hEps
  . exact avram_jump6_B_original_topcap_strict_source_payment_residual_cash_epsilon
      X x C hC hTop q hq w hw_cont hw_smooth hw_grad
      D hD ω t hStrict n ht
