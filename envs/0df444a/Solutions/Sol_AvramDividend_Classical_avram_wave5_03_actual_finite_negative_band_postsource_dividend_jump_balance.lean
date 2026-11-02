-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_finite_negative_band_postsource_dividend_jump_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:47:51.546124+00:00
-- url     : https://prove2.me/submissions/3ef6145a-879e-4249-83bf-0150128ef60b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_riskProcess_finite_band_ito_jump_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (u v ζ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (S : Finset ℝ≥0)
    (hS : ∀ r : ℝ≥0, r ∈ S ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B) :
    let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
    let J : ℝ≥0 → ℝ := fun r =>
      X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
    let W : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X r ω - rightLimit D r ω
      else riskProcess X x D r ω
    let cash : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        rightLimit D r ω - D r ω else 0
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y r ∈ Icc (u + ζ) v then
        (w (W r) - w (Function.leftLim
          (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r
       else 0) else 0) ≤
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if -1 < J r then
        J r * (if Y r ∈ Icc (u + ζ) v then deriv w (Y r) else 0)
       else 0) +
      (if Y r ∈ Icc (u + ζ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r)
       else 0)
      else 0) := by
  dsimp only
  let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
    (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
  let J : ℝ≥0 → ℝ := fun r =>
    X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
  let W : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X r ω - rightLimit D r ω
    else riskProcess X x D r ω
  let cash : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) < ruinTime X x D ω then
      rightLimit D r ω - D r ω else 0
  have hSourceFinite :=
    avram_wave5_03b_actual_stopped_riskProcess_finite_band_ito_jump_balance
      X x D hD.1.1 w u v ζ s t ω B hBneg S hS
  dsimp only at hSourceFinite
  calc
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y r ∈ Icc (u + ζ) v then
        (w (W r) - w (Function.leftLim
          (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r
       else 0) else 0) ≤
      (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y r ∈ Icc (u + ζ) v then
          w (riskProcess X x D r ω) -
            w (Function.leftLim
              (fun a : ℝ≥0 => riskProcess X x D a ω) r)
         else 0) else 0) := by
        apply Finset.sum_le_sum
        intro r hr
        by_cases hs : (r : ℝ≥0∞) ≤ ruinTime X x D ω
        · simp only [if_pos hs]
          by_cases hb : Y r ∈ Icc (u + ζ) v
          · simp only [if_pos hb]
            by_cases hp : (r : ℝ≥0∞) < ruinTime X x D ω
            · let R : ℝ := riskProcess X x D r ω
              let d : ℝ := rightLimit D r ω - D r ω
              have hAtom : d ≤ w R - w (R - d) :=
                (avram_wave5_03_original_separate_gradient_right_atom_control
                  X w C hC hw_cont hw_smooth hw_grad x hxc D hD)
                  ω r (Or.inr hp)
              have hPay : x + X.X r ω - rightLimit D r ω = R - d := by
                dsimp [R, d, riskProcess]
                ring
              dsimp [W, cash]
              simp only [if_pos hp]
              rw [hPay]
              linarith
            · dsimp [W, cash]
              simp only [if_neg hp, add_zero]
              exact le_refl _
          · simp only [if_neg hb]
            exact le_refl _
        · simp only [if_neg hs]
          exact le_refl _
    _ = _ := hSourceFinite
