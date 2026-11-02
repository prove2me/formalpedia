-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_weighted_full_stieltjes_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:09:52.287028+00:00
-- url     : https://prove2.me/submissions/21c7db19-a479-41a4-9c72-daf353ba9a6a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hgrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (weight : ℕ → ℝ≥0∞) :
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i : ℝ) (u (i + 1) : ℝ)).indicator
        (fun _ : ℝ => weight (i + 1)) t
      ∂dividendMeasure D ω) ≤
    ∑ i ∈ Finset.range n,
      weight (i + 1) * ENNReal.ofReal (
        (if x + X.X (u (i + 1)) ω - rightLimit D (u i) ω ≤ c
          then w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)
          else w c +
            ((x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) - c)) -
        (if x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω ≤ c
          then w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
          else w c +
            ((x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) - c))) := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  rw [avram_wave4_03_rightEndpoint_dividendMeasure_simpleGrid_lintegral
    D hStrategy ω u n weight]
  apply Finset.sum_le_sum
  intro i hi
  have hii : i < n := Finset.mem_range.mp hi
  have hJump := hAdmissible.2 ω (u (i + 1)) (hPre i hii)
  have hCover : rightLimit D (u (i + 1)) ω ≤
      x + X.X (u (i + 1)) ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  have hmono : rightLimit D (u i) ω ≤
      rightLimit D (u (i + 1)) ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone
      D hStrategy ω) (hgrid i hii)
  have hpost : 0 ≤
      x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω :=
    sub_nonneg.mpr hCover
  have horder :
      x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω ≤
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω := by
    linarith only [hmono]
  have hsec := avram_wave4_04_cap_linear_extension_full_secant
    c hc w hw_cont hw_smooth hw_grad
    (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
    (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)
    hpost horder
  have hdrop : rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω ≤
      (if x + X.X (u (i + 1)) ω - rightLimit D (u i) ω ≤ c
        then w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)
        else w c +
          ((x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) - c)) -
      (if x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω ≤ c
        then w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
        else w c +
          ((x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) - c)) := by
    linarith only [hsec]
  simpa only [mul_comm] using
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hdrop) (weight (i + 1)))
