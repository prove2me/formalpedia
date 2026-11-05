-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_source_cell_caplinear_raw_jump_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:11:56.216531+00:00
-- url     : https://prove2.me/submissions/0fce2e0e-d872-44a8-95f2-166a321d89d4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_monotone_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_cell_raw_jump_residual_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- The original continuous BV residual can only decrease the cap-linear
   frozen-dividend source value, retaining the actual negative jump sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (i : ℕ),
      u i ≤ u (i + 1) →
      0 ≤ x + X.X (u (i + 1)) ω - rightLimit D (u i) ω →
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        V (x + X.X (u i) ω - rightLimit D (u i) ω) ≤
      V ((x + X.X (u i) ω - rightLimit D (u i) ω) +
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
        (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
         else 0)) -
        V (x + X.X (u i) ω - rightLimit D (u i) ω) := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  have hVm : MonotoneOn V (Ici (0 : ℝ)) :=
    avram_p3_bv_allcap_linear_monotone_nonnegative
      C hC w hw_cont hw_smooth hw_grad
  filter_upwards [
      avram_p3_bv_original_source_cell_raw_jump_residual_identity X hBV x D,
      avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV]
    with ω hCell hR
  intro u i hui hZ
  have hRaw := hCell u i hui
  have hRinc := hR hui
  dsimp at hRaw hRinc
  have hZle :
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω ≤
      (x + X.X (u i) ω - rightLimit D (u i) ω) +
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
        (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
         else 0) := by
    linarith
  have hValue := hVm (mem_Ici.mpr hZ)
    (mem_Ici.mpr (le_trans hZ hZle)) hZle
  dsimp [V] at hValue ⊢
  linarith
