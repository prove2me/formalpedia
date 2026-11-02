-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_discounted_chronological_levy_then_dividend_generator_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:36:48.912083+00:00
-- url     : https://prove2.me/submissions/7e9cb40d-0079-4287-80ca-f69d8825f68d

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

/-- At a genuine negative source jump before ruin, first apply the
original Lévy source increment, then the admissible chronological right
dividend. The discounted combined nonlinear jump+cash does not exceed
the exact source linear mark plus generator Taylor remainder. -/
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
    (htRuin : (t : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q)
    (u v ζ : ℝ) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let J : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    ∀ (hJneg : J < 0) (hBand : Y ∈ Icc (u + ζ) v),
    Real.exp (-(q * (t : ℝ))) *
      ((w (x + X.X t ω - rightLimit D t ω) -
          w (Function.leftLim (fun s : ℝ≥0 =>
            riskProcess X x D s ω) t)) +
        (rightLimit D t ω - D t ω)) ≤
    Real.exp (-(q * (t : ℝ))) *
      ((if -1 < J then J * deriv w Y else 0) +
        SpectrallyNegativeLevy.generatorIntegrand w Y J) := by
  dsimp only
  let Y : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let J : ℝ :=
    X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
  intro hJneg hBand
  let R : ℝ := riskProcess X x D t ω
  let d : ℝ := rightLimit D t ω - D t ω
  let L : ℝ := Function.leftLim (fun s : ℝ≥0 => riskProcess X x D s ω) t
  have hPay : x + X.X t ω - rightLimit D t ω = R - d := by
    dsimp [R, d, riskProcess]
    ring
  have hAtom : d ≤ w R - w (R - d) :=
    (avram_wave5_03_original_separate_gradient_right_atom_control
      X w C hC hw_cont hw_smooth hw_grad x hxc D hD)
      ω t (Or.inr htRuin)
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
  have hBase :
      (w (R - d) - w L) + d ≤
      (if -1 < J then J * deriv w Y else 0) +
        SpectrallyNegativeLevy.generatorIntegrand w Y J := by
    linarith [hAtom, hSource, hKernel]
  rw [hPay]
  exact mul_le_mul_of_nonneg_left hBase (le_of_lt (Real.exp_pos _))
