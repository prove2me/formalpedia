-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_BV_complement_stopped_negative_source_mark_positivepart_lintegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:38:12.59005+00:00
-- url     : https://prove2.me/submissions/68aec5c1-4a7a-435d-a3a7-11a6b3b6efad

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (T : ℝ≥0) :
    let μ : Measure ((ℝ≥0 × Ω) × ℝ) :=
      (((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P).prod X.ν)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t p.2 - rightLimit D t p.2) p.1
    let S : Set ((ℝ≥0 × Ω) × ℝ) :=
      {p | p.1.1 ≤ T ∧
        (p.1.1 : ℝ≥0∞) < ruinTime X x D p.1.2 ∧
        0 < Y p.1 ∧ ENNReal.ofReal (Y p.1) < C ∧ p.2 < 0}
    MeasurableSet S →
    (∫⁻ p in S, ENNReal.ofReal
      (Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1))) ∂μ) = 0 := by
  dsimp only
  intro hS
  let μ : Measure ((ℝ≥0 × Ω) × ℝ) :=
    (((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P).prod X.ν)
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun t : ℝ≥0 =>
      x + X.X t p.2 - rightLimit D t p.2) p.1
  let S : Set ((ℝ≥0 × Ω) × ℝ) :=
    {p | p.1.1 ≤ T ∧
      (p.1.1 : ℝ≥0∞) < ruinTime X x D p.1.2 ∧
      0 < Y p.1 ∧ ENNReal.ofReal (Y p.1) < C ∧ p.2 < 0}
  have hzero : (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      ENNReal.ofReal (Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1)))) =ᵐ[μ.restrict S]
      (fun _ => (0 : ℝ≥0∞)) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    rcases hp with ⟨_, _, hy0, hyC, hz⟩
    let y : ℝ := Y p.1
    have hyCapBound : ENNReal.ofReal y ≤ C := le_of_lt hyC
    have hSec0 :=
      avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad 0 y
        (le_refl (0 : ℝ)) (le_of_lt hy0) hyCapBound
    have hwy : 0 ≤ w y := by linarith
    have hLoss : w (Y p.1 + p.2) - w (Y p.1) ≤ 0 := by
      by_cases hneg : y + p.2 < 0
      · have hwneg : w (y + p.2) = 0 := hw_neg _ hneg
        dsimp only [y] at hwneg hwy
        rw [hwneg]
        linarith
      · have hres0 : 0 ≤ y + p.2 := le_of_not_gt hneg
        have hresle : y + p.2 ≤ y := by linarith
        have hSecStep :=
          avram_wave3_03_bv_full_cap_gradient_secant
            C hC w hw_cont hw_smooth hw_grad (y + p.2) y
            hres0 hresle hyCapBound
        dsimp only [y] at hSecStep
        linarith
    have hExp : 0 ≤ Real.exp (-(q * (p.1.1 : ℝ))) :=
      le_of_lt (Real.exp_pos _)
    exact ENNReal.ofReal_eq_zero.mpr
      (mul_nonpos_of_nonneg_of_nonpos hExp hLoss)
  calc
    (∫⁻ p in S, ENNReal.ofReal
      (Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1))) ∂μ) =
      (∫⁻ p in S, (0 : ℝ≥0∞) ∂μ) := lintegral_congr_ae hzero
    _ = 0 := by simp
