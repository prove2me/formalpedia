-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_psi_above_of_gap_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T14:16:34.83285+00:00
-- url     : https://prove2.me/submissions/16ca651f-fce8-410e-bdf1-2a3c1fee7174

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_lower_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option autoImplicit false

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (N : ℕ)
    (hJN : (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) -
      (X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0)))) / 4 <
      (∫ y : ℝ, (Real.exp (((N : ℝ) + 1) * y) - 1 - ((N : ℝ) + 1) * y) /
        ((N : ℝ) + 1) ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))
    (hqN : q / ((N : ℝ) + 1) < (X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0)))) / 4)
    (hBN : (∫ _ in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) / ((N : ℝ) + 1) <
      (X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0)))) / 4)
    (hmono : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
      (∫ y : ℝ, (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) ≤
      (∫ y : ℝ, (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))
    (hBV : X.BoundedVariation) :
    ∀ θ : ℝ, ((N : ℝ) + 1) ≤ θ → q < X.ψ θ := by
  intro θ hNθ
  let a : ℝ := (N : ℝ) + 1
  let A := ∫ y in Ioo (-1 : ℝ) 0, |y| ∂X.ν
  let B := ∫ _ in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν
  let J (s : ℝ) := ∫ y in Ioo (-1 : ℝ) 0, (Real.exp (s * y) - 1 - s * y) / s ∂X.ν
  let ε := (X.c + A) / 4
  change A - ε < J a at hJN
  change q / a < ε at hqN
  change B / a < ε at hBN
  change a ≤ θ at hNθ
  have ha : 0 < a := by dsimp [a]; positivity
  have hθ : 0 < θ := ha.trans_le hNθ
  have hB : 0 ≤ B := integral_nonneg (fun _ => zero_le_one)
  have hq' : q / θ < ε := (div_le_div_of_nonneg_left hq.le ha hNθ).trans_lt hqN
  have hB' : B / θ < ε := (div_le_div_of_nonneg_left hB ha hNθ).trans_lt hBN
  have hJ : A - ε < J θ := hJN.trans_le (hmono a θ ha hNθ)
  have hΨ := psi_lower_bound_by_compensated_small_jumps X θ hθ.le
    (levy_large_negative_jump_unit_integrable X)
  simp only [hBV.1, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div, add_zero] at hΨ
  have hnorm := div_le_div_of_nonneg_right hΨ hθ.le
  rw [sub_div, add_div, mul_div_cancel_right₀ _ hθ.ne', ← integral_div] at hnorm
  change X.c + J θ - B / θ ≤ X.ψ θ / θ at hnorm
  have hlt : q / θ < X.c + J θ - B / θ := by
    have hqpos : 0 < q / θ := div_pos hq hθ
    dsimp [ε] at hq' hB' hJ
    linarith only [hq', hB', hJ, hqpos]
  exact (div_lt_div_iff_of_pos_right hθ).mp (hlt.trans_le hnorm)
