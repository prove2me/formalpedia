-- Prove2me | solution 1 for AvramDividend.Classical.avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:23:19.262884+00:00
-- url     : https://prove2.me/submissions/9be85955-de49-4707-9fe1-2099fa805c44

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b240_original_ruinclipped_mixed_allcap_discounted_full_stieltjes_source_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨
      (b : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let Y : ℝ := x + X.X b ω - rightLimit D b ω
    let Z : ℝ := x + X.X b ω - rightLimit D a ω
    (∫⁻ t in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (b : ℝ))) * (V Y - V Z) ≤
      (Real.exp (-(q * (a : ℝ))) -
       Real.exp (-(q * (b : ℝ)))) * (V Z - V Y) := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else
    if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  let Y : ℝ := x + X.X b ω - rightLimit D b ω
  let Z : ℝ := x + X.X b ω - rightLimit D a ω
  have hLeft :=
    avram_b240_original_ruinclipped_mixed_allcap_discounted_full_stieltjes_source_sign
      X x q hq C hC w hw_cont hw_smooth hw_grad
      D hD ω a b hab hPre
  change
    (∫⁻ t in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) * (V Y - V Z) ≤ 0 at hLeft
  change
    (∫⁻ t in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (b : ℝ))) * (V Y - V Z) ≤
      (Real.exp (-(q * (a : ℝ))) -
       Real.exp (-(q * (b : ℝ)))) * (V Z - V Y)
  nlinarith only [hLeft]
