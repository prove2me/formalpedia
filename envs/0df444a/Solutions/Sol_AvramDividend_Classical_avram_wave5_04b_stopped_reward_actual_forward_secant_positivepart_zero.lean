-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_stopped_reward_actual_forward_secant_positivepart_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:51:34.27023+00:00
-- url     : https://prove2.me/submissions/0eaa0041-a4b5-4967-be4b-ff97168c3b3b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The positive part of the signed Stieltjes forward-secant control vanishes
on the full original ruin-stopped payment domain with no integrability premise;
time zero, boundary contacts and singular-continuous variation are retained. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q δ : ℝ) (hδ : 0 < δ) (w V : ℝ → ℝ)
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
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T)
    : (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
          V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))) ∂(dividendMeasure D ω)) = 0 := by
  have hPoint : ∀ s : ℝ, s ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T →
      Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ≤ 0 := by
    intro s hs
    have hsPay := hs.1
    change s ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {t : ℝ | ENNReal.ofReal t < ruinTime X x D ω}) at hsPay
    have hPreS : s.toNNReal = 0 ∨
        (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
      rcases hsPay.2 with hzero | hlt
      · left
        have heq : s = 0 := by simpa using hzero
        simp only [heq, Real.toNNReal_zero]
      · right
        change (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω at hlt
        exact hlt
    have hAdmissible : IsAdmissible X x D := hD.1
    have hCover := hAdmissible.2 ω s.toNNReal hPreS
    dsimp [riskProcess] at hCover
    let y : ℝ := x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω
    have hy : 0 ≤ y := by linarith only [hCover]
    have hOrder : y ≤ y + δ := le_add_of_nonneg_right hδ.le
    have hSec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
      C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      y (y + δ) hy hOrder
    have hResidual : δ + V y - V (y + δ) ≤ 0 := by
      linarith only [hSec]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual
  calc
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
          V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))) ∂(dividendMeasure D ω))
      = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          (0 : ℝ≥0∞) ∂(dividendMeasure D ω)) := by
            apply MeasureTheory.lintegral_congr_ae
            filter_upwards [MeasureTheory.ae_restrict_mem
              (MeasurableSet.inter (paymentTimes_measurable _) measurableSet_Iic)] with s hs
            exact ENNReal.ofReal_eq_zero.mpr (hPoint s hs)
    _ = 0 := by simp
