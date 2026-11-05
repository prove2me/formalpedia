-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_live_grid_expected_budget_of_source_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:41:16.744445+00:00
-- url     : https://prove2.me/submissions/92c5d1f7-0fa7-482c-a69a-168689f2974a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_grid_full_w_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Expected original physical finite-grid verification: the actual closed
   Stieltjes cash and postpayment w terminal are bounded whenever the
   fully displayed cap-linear source correction has nonpositive mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hLive : ∀ᵐ ω ∂P, (u n : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : Ω → ℝ≥0 → ℝ := fun ω t =>
      x + X.X t ω - rightLimit D t ω
    let Z : Ω → ℕ → ℝ := fun ω i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    let CashTerm : Ω → ℝ := fun ω =>
      E (u n) * w (Y ω (u n)) +
        (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
    let Source : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range n,
        ((E (u (i + 1)) - E (u i)) * V (Y ω (u (i + 1))) +
          E (u i) * (V (Z ω i) - V (Y ω (u i))))
    Integrable CashTerm P →
      Integrable Source P →
      Integrable (fun _ : Ω => w x) P →
      (∫ ω, Source ω ∂P) ≤ 0 →
      (∫ ω, CashTerm ω ∂P) ≤
        (∫ _ : Ω, w x ∂P) := by
  intro V E Y Z CashTerm Source hCashInt hSourceInt hConstInt hSourceMean
  have hPath : ∀ᵐ ω ∂P, CashTerm ω ≤ w x + Source ω := by
    filter_upwards [hLive] with ω hω
    have hPre : ∀ i : ℕ, i < n →
        u (i + 1) = 0 ∨
          (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
      intro i hi
      right
      exact (ENNReal.coe_le_coe.mpr (hu (Nat.succ_le_of_lt hi))).trans_lt hω
    exact avram_p3_bv_original_closed_grid_full_w_budget
      X x hx C hC hxc q hq w hw_cont hw_smooth hw_grad
      D hD ω u n hu hu0 hPre
  have hExpected := integral_mono_ae hCashInt (hConstInt.add hSourceInt) hPath
  simp only [Pi.add_apply] at hExpected
  rw [integral_add hConstInt hSourceInt] at hExpected
  linarith
