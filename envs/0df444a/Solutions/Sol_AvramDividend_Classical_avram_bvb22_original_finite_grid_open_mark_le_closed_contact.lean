-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_original_finite_grid_open_mark_le_closed_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T13:39:27.124219+00:00
-- url     : https://prove2.me/submissions/67367669-9c8b-46d5-b40a-84a9ecc5ce22

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n : ℕ) (ω : Ω) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    let A : ℝ := ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ Z i ∧ ENNReal.ofReal (Z i) ≤ C then
        Real.exp (-(q * (u n i : ℝ))) * ψ (Z i) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    let J : ℝ := ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) * ψ (Z i) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    A ≤ J := by
  intro Z ψ A J
  dsimp only [A, J]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hOpen : (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Z i ∧ ENNReal.ofReal (Z i) < C
  · have hClosed : (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 ≤ Z i ∧ ENNReal.ofReal (Z i) ≤ C :=
      ⟨hOpen.1, le_of_lt hOpen.2.1, le_of_lt hOpen.2.2⟩
    simp only [if_pos hOpen, if_pos hClosed, le_refl]
  · by_cases hClosed : (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 ≤ Z i ∧ ENNReal.ofReal (Z i) ≤ C
    · have hPsi : ψ (Z i) ≤ 0 := by
        dsimp [ψ]
        exact avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
          C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
          X.ν (Z i) hClosed.2.1 hClosed.2.2
      have hStep : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) := by
        apply sub_nonneg.mpr
        exact_mod_cast hmono n i (Finset.mem_range.mp hi)
      have hTerm :
          Real.exp (-(q * (u n i : ℝ))) * ψ (Z i) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos
            (le_of_lt (Real.exp_pos _)) hPsi) hStep
      simpa only [if_pos hClosed, if_neg hOpen] using hTerm
    · simp only [if_neg hClosed, if_neg hOpen, le_refl]
