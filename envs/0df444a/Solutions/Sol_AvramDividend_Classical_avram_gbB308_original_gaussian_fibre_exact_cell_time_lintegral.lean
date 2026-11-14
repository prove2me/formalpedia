-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB308_original_gaussian_fibre_exact_cell_time_lintegral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:17:04.279488+00:00
-- url     : https://prove2.me/submissions/c8574163-ad2c-49a2-bcb1-257718327008
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB311_exact_original_gaussian_physical_time_kernel_factor
import Theorems.Thm_AvramDividend_Classical_avram_gbB312_scaled_translated_gaussian_open_cell_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_gbB313_exact_original_gaussian_single_cell_prefactor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (sigma : ℝ) (hsigma : 0 < sigma)
    (m i : ℕ) (hm : 0 < m) :
    (∫⁻ t in Set.Ioo
        ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))),
      ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi *
          (((NNReal.mk (sigma ^ 2) (sq_nonneg sigma)) *
            ((Real.toNNReal t -
              ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) : ℝ≥0) : NNReal) : ℝ))))⁻¹) *
      ENNReal.ofReal (1 / ((m : ℝ) ^ 3)) ∂volume) ≤
      (Real.toNNReal (2 /
        (sigma * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5))) : ℝ≥0∞) := by
  let s : ℝ := (i : ℝ) * (1 / ((m : ℝ) ^ 4))
  let δ : ℝ := 1 / ((m : ℝ) ^ 4)
  let C : ℝ≥0∞ :=
    ENNReal.ofReal (1 / (sigma * Real.sqrt (2 * Real.pi))) *
      ENNReal.ofReal (1 / ((m : ℝ) ^ 3))
  let F : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi *
        (((NNReal.mk (sigma ^ 2) (sq_nonneg sigma)) *
          ((Real.toNNReal t -
            ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) : ℝ≥0) : NNReal) : ℝ))))⁻¹) *
    ENNReal.ofReal (1 / ((m : ℝ) ^ 3))
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hright :
      (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) = s + δ := by
    dsimp [s, δ]
    ring
  have hCpos : 0 ≤ 1 / (sigma * Real.sqrt (2 * Real.pi)) := by positivity
  have hF (t : ℝ) (ht : t ∈ Set.Ioo s (s + δ)) :
      F t = C * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) := by
    have hKernel :=
      avram_gbB311_exact_original_gaussian_physical_time_kernel_factor
        sigma hsigma m i hm t (by simpa only [s, δ, ← hright] using ht)
    change
      ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi *
          (((NNReal.mk (sigma ^ 2) (sq_nonneg sigma)) *
            ((Real.toNNReal t -
              ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) : ℝ≥0) : NNReal) : ℝ))))⁻¹) *
        ENNReal.ofReal (1 / ((m : ℝ) ^ 3)) =
      (ENNReal.ofReal (1 / (sigma * Real.sqrt (2 * Real.pi))) *
        ENNReal.ofReal (1 / ((m : ℝ) ^ 3))) *
          ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ)))
    rw [hKernel, ENNReal.ofReal_mul hCpos]
    ac_rfl
  have hTime :
      (∫⁻ t in Set.Ioo s (s + δ), F t ∂volume) ≤
        C * ENNReal.ofReal (2 * Real.sqrt δ) := by
    calc
      (∫⁻ t in Set.Ioo s (s + δ), F t ∂volume) =
          ∫⁻ t in Set.Ioo s (s + δ),
            C * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) ∂volume := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
              exact hF t ht
      _ ≤ C * ENNReal.ofReal (2 * Real.sqrt δ) :=
        avram_gbB312_scaled_translated_gaussian_open_cell_lintegral
          s δ hδ C
  have hCoeff : C * ENNReal.ofReal (2 * Real.sqrt δ) =
      (Real.toNNReal (2 /
        (sigma * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5))) : ℝ≥0∞) := by
    exact avram_gbB313_exact_original_gaussian_single_cell_prefactor
      sigma hsigma m hm
  simpa only [s, δ, F, hright] using hTime.trans_eq hCoeff
