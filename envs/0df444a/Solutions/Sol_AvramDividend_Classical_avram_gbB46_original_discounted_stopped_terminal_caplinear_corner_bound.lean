-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB46_original_discounted_stopped_terminal_caplinear_corner_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:26:14.930631+00:00
-- url     : https://prove2.me/submissions/1c6dafcb-4a3b-479d-bedc-2b09181700a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB44_original_admissible_finitecap_postpayment_terminal_corner_gap
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
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (t : ℝ≥0)
    (hy0 : 0 ≤ x + X.X t ω - rightLimit D t ω) :
    let y : ℝ := x + X.X t ω - rightLimit D t ω
    let V : ℝ → ℝ := fun z =>
      if z ≤ b then w z else w b + (z - b)
    0 ≤ Real.exp (-(q * (t : ℝ))) * (w y - V y) ∧
      Real.exp (-(q * (t : ℝ))) * (w y - V y) ≤
        (w C.toReal - w b) - (C.toReal - b) := by
  let y : ℝ := x + X.X t ω - rightLimit D t ω
  let V : ℝ → ℝ := fun z =>
    if z ≤ b then w z else w b + (z - b)
  change 0 ≤ Real.exp (-(q * (t : ℝ))) * (w y - V y) ∧
    Real.exp (-(q * (t : ℝ))) * (w y - V y) ≤
      (w C.toReal - w b) - (C.toReal - b)
  have hGap :=
    avram_gbB44_original_admissible_finitecap_postpayment_terminal_corner_gap
      X x C hC hFiniteCap hxc D hD w hw_cont hw_smooth hw_grad
      b hb0 hbC ω t hy0
  have hEpos : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have hqt : 0 ≤ q * (t : ℝ) := mul_nonneg hq (NNReal.coe_nonneg t)
  have hEle : Real.exp (-(q * (t : ℝ))) ≤ 1 :=
    (Real.exp_le_one_iff).2 (neg_nonpos.mpr hqt)
  refine ⟨mul_nonneg hEpos hGap.1, ?_⟩
  have hWeighted : Real.exp (-(q * (t : ℝ))) * (w y - V y) ≤
      w y - V y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hEle) hGap.1]
  exact le_trans hWeighted hGap.2
