-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_original_expected_full_stieltjes_grid_source_drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:57:47.590533+00:00
-- url     : https://prove2.me/submissions/badb1fa2-95e2-426a-901e-40901888fd96

import Theorems.Thm_avram_wave5_03_actual_original_expected_full_stieltj_pointwise_upper_bound_75183679
import Theorems.Thm_avram_wave5_03_actual_original_expected_full_stieltj_pointwise_upper_bound_448b4247
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ ω (i : ℕ), i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (hCashInt : Integrable (fun ω => (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (hSourceInt : Integrable (fun ω =>
      ∑ i ∈ Finset.range n,
          ((Real.exp (-(q * (u (i + 1) : ℝ))) -
              Real.exp (-(q * (u i : ℝ)))) *
              V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) +
            Real.exp (-(q * (u i : ℝ))) *
              (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
                V (x + X.X (u i) ω - rightLimit D (u i) ω)))) P) :
    (∫ ω, (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
      V x + (∫ ω, ∑ i ∈ Finset.range n,
          ((Real.exp (-(q * (u (i + 1) : ℝ))) -
              Real.exp (-(q * (u i : ℝ)))) *
              V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) +
            Real.exp (-(q * (u i : ℝ))) *
              (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
                V (x + X.X (u i) ω - rightLimit D (u i) ω))) ∂P) := by

  letI : IsProbabilityMeasure P := X.isProbability
  let cash : Ω → ℝ := fun ω => (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
    ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let source : Ω → ℝ := fun ω => ∑ i ∈ Finset.range n, ((Real.exp (-(q * (u (i + 1) : ℝ))) - Real.exp (-(q * (u i : ℝ)))) * V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) + Real.exp (-(q * (u i : ℝ))) * (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) - V (x + X.X (u i) ω - rightLimit D (u i) ω)))
  have ht := avram_wave5_03_actual_original_expected_full_stieltj_pointwise_upper_bound_75183679
    X x hx C hC hxc q hq w V hw0 hw_cont hw_neg hw_smooth hw_grad
    hVtop hVfinite D hD u n hu hu0 hPre hCashInt hSourceInt hCashInt hSourceInt
  have hp := avram_wave5_03_actual_original_expected_full_stieltj_pointwise_upper_bound_448b4247
    X x hx C hC hxc q hq w V hw0 hw_cont hw_neg hw_smooth hw_grad
    hVtop hVfinite D hD u n hu hu0 hPre hCashInt hSourceInt hCashInt hSourceInt ht
  have hci : Integrable cash P := hCashInt
  have hsi : Integrable source P := hSourceInt
  have hm : (∫ ω, cash ω ∂P) ≤ (∫ ω, V x + source ω ∂P) :=
    integral_mono hci ((integrable_const _).add hsi) hp
  change (∫ ω, cash ω ∂P) ≤ V x + (∫ ω, source ω ∂P)
  calc
    _ ≤ (∫ ω, V x + source ω ∂P) := hm
    _ = V x + (∫ ω, source ω ∂P) := by simp [integral_add, hsi]
