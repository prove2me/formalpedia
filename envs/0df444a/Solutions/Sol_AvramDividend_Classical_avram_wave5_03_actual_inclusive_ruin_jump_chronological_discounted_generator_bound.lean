-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_inclusive_ruin_jump_chronological_discounted_generator_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:41:44.356093+00:00
-- url     : https://prove2.me/submissions/6ee4fe75-4f64-4099-b4f4-56710f0d3d61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Include a source negative mark at the genuine stopped ruin instant, but
exclude the inadmissible positive-ruin right payment. Before ruin, pay the
chronological right dividend after the original source jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (htStop : (t : ℝ≥0∞) ≤ ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q)
    (u v ζ : ℝ) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let J : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let W : ℝ :=
      if (t : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    let cash : ℝ :=
      if (t : ℝ≥0∞) < ruinTime X x D ω then
        rightLimit D t ω - D t ω else 0
    ∀ (hJneg : J < 0) (hBand : Y ∈ Icc (u + ζ) v),
    Real.exp (-(q * (t : ℝ))) *
      ((w W -
          w (Function.leftLim (fun s : ℝ≥0 =>
            riskProcess X x D s ω) t)) + cash) ≤
    Real.exp (-(q * (t : ℝ))) *
      ((if -1 < J then J * deriv w Y else 0) +
        SpectrallyNegativeLevy.generatorIntegrand w Y J) := by
  dsimp only
  let Y : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let J : ℝ :=
    X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
  let W : ℝ :=
    if (t : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X t ω - rightLimit D t ω
    else riskProcess X x D t ω
  let cash : ℝ :=
    if (t : ℝ≥0∞) < ruinTime X x D ω then
      rightLimit D t ω - D t ω else 0
  intro hJneg hBand
  let R : ℝ := riskProcess X x D t ω
  let d : ℝ := rightLimit D t ω - D t ω
  let L : ℝ := Function.leftLim (fun s : ℝ≥0 => riskProcess X x D s ω) t
  have hSource : w R - w L = w (Y + J) - w Y := by
    exact avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
      X x D hD.1.1 w ω t ht
  have hKernel :
      w (Y + J) - w Y -
        (if -1 < J then J * deriv w Y else 0) =
      SpectrallyNegativeLevy.generatorIntegrand w Y J := by
    have hk := avram_wave5_03b_actual_source_taylor_generator_kernel_eq
      X x D hD.1.1 w u v ζ (t, ω) J hJneg
    simpa only [if_pos hBand] using hk
  have hRaw : w R - w L =
      (if -1 < J then J * deriv w Y else 0) +
        SpectrallyNegativeLevy.generatorIntegrand w Y J := by
    linarith [hSource, hKernel]
  have hChron : (w W - w L) + cash ≤ w R - w L := by
    by_cases hp : (t : ℝ≥0∞) < ruinTime X x D ω
    · have hAtom : d ≤ w R - w (R - d) :=
        (avram_wave5_03_original_separate_gradient_right_atom_control
          X w C hC hw_cont hw_smooth hw_grad x hxc D hD)
          ω t (Or.inr hp)
      have hPay : x + X.X t ω - rightLimit D t ω = R - d := by
        dsimp [R, d, riskProcess]
        ring
      dsimp [W, cash]
      simp only [if_pos hp]
      rw [hPay]
      linarith
    · dsimp [W, cash]
      simp only [if_neg hp, add_zero]
      exact le_refl _
  have hTotal :
      (w W - w L) + cash ≤
        (if -1 < J then J * deriv w Y else 0) +
          SpectrallyNegativeLevy.generatorIntegrand w Y J := by
    calc
      (w W - w L) + cash ≤ w R - w L := hChron
      _ = _ := hRaw
  exact mul_le_mul_of_nonneg_left hTotal (le_of_lt (Real.exp_pos _))
