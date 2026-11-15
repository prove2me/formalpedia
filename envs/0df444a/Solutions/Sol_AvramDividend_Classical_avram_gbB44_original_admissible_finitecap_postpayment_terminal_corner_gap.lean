-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB44_original_admissible_finitecap_postpayment_terminal_corner_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:13:30.968318+00:00
-- url     : https://prove2.me/submissions/6b26cb4d-c8ab-468c-9766-019ca9d71dba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB43_original_finitecap_terminal_caplinear_gap_bounded_by_corner
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
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
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (b : ℝ) (hb0 : 0 ≤ b) (hbC : b ≤ C.toReal)
    (ω : Ω) (t : ℝ≥0)
    (hy0 : 0 ≤ x + X.X t ω - rightLimit D t ω) :
    let y : ℝ := x + X.X t ω - rightLimit D t ω
    let V : ℝ → ℝ := fun z =>
      if z ≤ b then w z else w b + (z - b)
    0 ≤ w y - V y ∧
      w y - V y ≤ (w C.toReal - w b) - (C.toReal - b) := by
  let y : ℝ := x + X.X t ω - rightLimit D t ω
  let V : ℝ → ℝ := fun z =>
    if z ≤ b then w z else w b + (z - b)
  change 0 ≤ w y - V y ∧
    w y - V y ≤ (w C.toReal - w b) - (C.toReal - b)
  have hyCap : ENNReal.ofReal y ≤ C := by
    simpa only [y] using
      capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t
  have hyC : y ≤ C.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hFiniteCap).1 hyCap
  exact avram_gbB43_original_finitecap_terminal_caplinear_gap_bounded_by_corner
    C hC hFiniteCap w hw_cont hw_smooth hw_grad
    b y hb0 hbC hy0 hyC hyCap
