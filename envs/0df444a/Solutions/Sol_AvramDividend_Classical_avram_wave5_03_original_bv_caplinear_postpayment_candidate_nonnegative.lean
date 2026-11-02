-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_bv_caplinear_postpayment_candidate_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:32:03.776649+00:00
-- url     : https://prove2.me/submissions/43f95f2a-0186-46a5-99eb-846220e3fd0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap

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
    (w V : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ V (x + X.X t ω - rightLimit D t ω) := by
  let z : ℝ := x + X.X t ω - rightLimit D t ω
  have hw : 0 ≤ w z :=
    avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
      X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD ω t
  have hcap : ENNReal.ofReal z ≤ C :=
    capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t
  change 0 ≤ V z
  by_cases hz0 : 0 ≤ z
  · have heq :=
      avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
        C hC w V hVtop hVfinite z hz0 hcap
    rw [heq]
    exact hw
  · have hzneg : z < 0 := lt_of_not_ge hz0
    by_cases htop : C = ⊤
    · rw [hVtop htop]
      exact hw
    · have hzcap : z ≤ C.toReal :=
        (le_of_lt hzneg).trans ENNReal.toReal_nonneg
      rw [hVfinite htop z, if_pos hzcap]
      exact hw
