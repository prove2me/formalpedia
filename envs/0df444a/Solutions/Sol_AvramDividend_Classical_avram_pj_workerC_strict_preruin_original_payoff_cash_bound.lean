-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_strict_preruin_original_payoff_cash_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:12:41.254236+00:00
-- url     : https://prove2.me/submissions/5379d824-a7d6-4e26-bde4-018da25001fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_strict_preruin_full_cash_at_true_endpoint
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
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
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (m : ℕ) :
    let u : ℕ → ℝ≥0 := fun i =>
      min (((i : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) * t) t
    let E : ℝ≥0 → ℝ := fun s => Real.exp (-(q * (s : ℝ)))
    let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (t) * w (Y (t)) +
      (∫⁻ s in Icc (0 : ℝ) ((t) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      w x +
        ∑ i ∈ Finset.range (m + 1),
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Z i) - V (Y (u i)))) := by
  have hpost : 0 ≤ x + X.X t ω - rightLimit D t ω := by
    exact avram_p4_e_localise_preruin_postpayment_nonnegative
      X x C D hD ω t (Or.inr ht)
  have hcap : ENNReal.ofReal
      (x + X.X t ω - rightLimit D t ω) ≤ C :=
    capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t
  have hVpost : V (x + X.X t ω - rightLimit D t ω) =
      w (x + X.X t ω - rightLimit D t ω) :=
    avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
      C hC w V hVtop hVfinite _ hpost hcap
  have hVx : V x = w x :=
    avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
      C hC w V hVtop hVfinite x hx hxc
  have hBound := avram_pj_workerC_strict_preruin_full_cash_at_true_endpoint
    X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω t ht m
  dsimp only at hBound ⊢
  rw [hVpost, hVx] at hBound
  exact hBound
