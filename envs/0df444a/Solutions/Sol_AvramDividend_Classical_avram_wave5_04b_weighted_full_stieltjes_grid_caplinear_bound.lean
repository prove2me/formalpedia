-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_weighted_full_stieltjes_grid_caplinear_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:09:36.446228+00:00
-- url     : https://prove2.me/submissions/4fde3782-b304-4e0b-8668-3b6562613ab0

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightEndpoint_dividendMeasure_simpleGrid_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hgrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (weight : ℕ → ℝ≥0∞) (y : ℕ → ℝ)
    (hy : ∀ i : ℕ, i < n → rightLimit D (u (i + 1)) ω ≤ y i) :
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i : ℝ) (u (i + 1) : ℝ)).indicator
        (fun _ : ℝ => weight (i + 1)) t
      ∂dividendMeasure D ω) ≤
    ∑ i ∈ Finset.range n,
      weight (i + 1) * ENNReal.ofReal (
        (if y i - rightLimit D (u i) ω ≤ c
          then w (y i - rightLimit D (u i) ω)
          else w c + ((y i - rightLimit D (u i) ω) - c)) -
        (if y i - rightLimit D (u (i + 1)) ω ≤ c
          then w (y i - rightLimit D (u (i + 1)) ω)
          else w c + ((y i - rightLimit D (u (i + 1)) ω) - c))) := by
  rw [avram_wave4_03_rightEndpoint_dividendMeasure_simpleGrid_lintegral
    D hD ω u n weight]
  apply Finset.sum_le_sum
  intro i hi
  have hii : i < n := Finset.mem_range.mp hi
  have hmono : rightLimit D (u i) ω ≤
      rightLimit D (u (i + 1)) ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone
      D hD ω) (hgrid i hii)
  have hpost : 0 ≤ y i - rightLimit D (u (i + 1)) ω :=
    sub_nonneg.mpr (hy i hii)
  have horder : y i - rightLimit D (u (i + 1)) ω ≤
      y i - rightLimit D (u i) ω := by
    linarith only [hmono]
  have hsec := avram_wave4_04_cap_linear_extension_full_secant
    c hc w hw_cont hw_smooth hw_grad
    (y i - rightLimit D (u (i + 1)) ω)
    (y i - rightLimit D (u i) ω) hpost horder
  have hdrop : rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω ≤
      (if y i - rightLimit D (u i) ω ≤ c
        then w (y i - rightLimit D (u i) ω)
        else w c + ((y i - rightLimit D (u i) ω) - c)) -
      (if y i - rightLimit D (u (i + 1)) ω ≤ c
        then w (y i - rightLimit D (u (i + 1)) ω)
        else w c + ((y i - rightLimit D (u (i + 1)) ω) - c)) := by
    linarith only [hsec]
  simpa only [mul_comm] using
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hdrop) (weight (i + 1)))
