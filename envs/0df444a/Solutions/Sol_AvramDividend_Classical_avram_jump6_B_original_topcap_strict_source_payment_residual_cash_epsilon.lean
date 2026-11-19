-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_topcap_strict_source_payment_residual_cash_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:42:53.534882+00:00
-- url     : https://prove2.me/submissions/963e50f3-f433-4351-ad67-4e934b16408a

import Mathlib
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
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
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
  intro eps heps
  have hParent :=
    avram_jump6_B_original_anycap_strict_canonical_caplinear_cash_epsilon
      X x C hC q hq w w hw_cont hw_smooth hw_grad
      (by intro _ y; rfl)
      (by intro hFalse; exact (hFalse hTop).elim)
      D hD ω t hStrict n ht eps heps
  filter_upwards [hParent] with j hj
  have hSwap :=
    avram_jump6_B_original_physical_payment_residual_signed_sum_rearrange
      X x q w D ω t n j
  dsimp only at hSwap hj
  linarith
