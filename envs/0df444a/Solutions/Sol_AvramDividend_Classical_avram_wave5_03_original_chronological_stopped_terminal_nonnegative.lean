-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_chronological_stopped_terminal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:01:21.182864+00:00
-- url     : https://prove2.me/submissions/fd9b6c1e-06e6-46ad-9e22-d78519de1117

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At the true finite stop, take the post-right-payment terminal state only
    on paid clocks (including zero), otherwise the original book reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0) :
    let τ : ℝ≥0∞ := ruinTime X x D ω
    let θ : ℝ≥0 := (min (T : ℝ≥0∞) τ).toNNReal
    let W : ℝ :=
      if θ = 0 ∨ (T : ℝ≥0∞) < τ then
        x + X.X θ ω - rightLimit D θ ω
      else riskProcess X x D θ ω
    0 ≤ w W := by
  dsimp only
  let τ : ℝ≥0∞ := ruinTime X x D ω
  let θ : ℝ≥0 := (min (T : ℝ≥0∞) τ).toNNReal
  let W : ℝ :=
    if θ = 0 ∨ (T : ℝ≥0∞) < τ then
      x + X.X θ ω - rightLimit D θ ω
    else riskProcess X x D θ ω
  change 0 ≤ w W
  have hcap : ENNReal.ofReal W ≤ C := by
    by_cases hp : θ = 0 ∨ (T : ℝ≥0∞) < τ
    · simpa only [W, if_pos hp] using
        (capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω θ)
    · have hθne : θ ≠ 0 := (not_or.mp hp).1
      have hθpos : 0 < θ :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ θ) (Ne.symm hθne)
      simpa only [W, if_neg hp] using (hD.2 ω θ hθpos)
  by_cases hy : 0 ≤ W
  · have hs : W - 0 ≤ w W - w 0 := by
      by_cases hBV : X.BoundedVariation
      · exact avram_wave3_03_bv_full_cap_gradient_secant
          C hC w hw_cont (hw_smooth.2 hBV) hw_grad 0 W
          (le_refl (0 : ℝ)) hy hcap
      · exact avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
          C w hw_cont (hw_smooth.1 hBV) hw_grad 0 W
          (le_refl (0 : ℝ)) hy hcap
    linarith
  · have hneg : W < 0 := lt_of_not_ge hy
    simp [hw_neg W hneg]
