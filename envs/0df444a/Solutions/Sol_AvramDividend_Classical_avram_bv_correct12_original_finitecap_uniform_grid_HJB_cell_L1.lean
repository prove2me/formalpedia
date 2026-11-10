-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_original_finitecap_uniform_grid_HJB_cell_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:29:28.904491+00:00
-- url     : https://prove2.me/submissions/32bfb604-bb54-4e5f-aa07-8f1cf92f226f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finitecap_generator_residual_floor
import Theorems.Thm_AvramDividend_Classical_avram_a19_generator_uniform_cell_aeStronglyMeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One actual uniform-grid HJB generator cell is integrable without B L1 premises. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (hMass : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n i : ℕ) (hi : i < n + 1) :
    Integrable (fun ω =>
      let Z : ℕ → ℝ := fun j => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, hR, hWbound⟩ :=
    avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
      w hw_cont (fun z hz => hw_neg z hz) C.toReal ENNReal.toReal_nonneg
  have hCoeff : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal + q :=
    add_nonneg ENNReal.toReal_nonneg hq.le
  have hDelta : 0 ≤ ((u n (i + 1) : ℝ) - (u n i : ℝ)) := by
    have hh := hmono n i hi
    exact sub_nonneg.mpr (by exact_mod_cast hh)
  have hWeight : 0 ≤
      Real.exp (-(q * (u n i : ℝ))) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ)) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hDelta
  have hMajor : Integrable (fun _ : Ω =>
      (Real.exp (-(q * (u n i : ℝ))) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))) *
        (((X.ν (Iio (0 : ℝ))).toReal + q) * R)) P := integrable_const _
  have hMeas := avram_a19_generator_uniform_cell_aeStronglyMeasurable
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT u hgrid hmono huniform n i hi
  apply hMajor.mono' hMeas
  filter_upwards [] with ω
  let Z : ℕ → ℝ := fun j => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
  by_cases hm : (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Z i ∧ ENNReal.ofReal (Z i) < C
  · have hy : 0 < Z i := hm.2.1
    have hyC : ENNReal.ofReal (Z i) < C := hm.2.2
    have hyB : Z i ≤ C.toReal := by
      simpa only [ENNReal.toReal_ofReal (le_of_lt hy)] using
        (ENNReal.toReal_mono hFinite (le_of_lt hyC))
    have hValue : w (Z i) ≤ R :=
      (le_abs_self _).trans (hWbound (Z i) hyB)
    have hGen := (hw_gen (Z i) hy hyC).1
    have hUpper := (hw_gen (Z i) hy hyC).2
    have hLower := avram_bv_correct12_finitecap_generator_residual_floor
      X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
        hMass (bv_standing_drift_pos X hX hBV).1.le (Z i) hy hyC hGen
    have hResidAbs : |X.generator w (Z i) - q * w (Z i)| ≤
        ((X.ν (Iio (0 : ℝ))).toReal + q) * R := by
      rw [abs_of_nonpos hUpper]
      have hh := mul_le_mul_of_nonneg_left hValue hCoeff
      linarith
    have hScaled := mul_le_mul_of_nonneg_left hResidAbs hWeight
    dsimp only [Z] at hm
    simp only [if_pos hm, Real.norm_eq_abs]
    calc
      |Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))| =
          (Real.exp (-(q * (u n i : ℝ))) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))) *
            |X.generator w (Z i) - q * w (Z i)| := by
              calc
                |Real.exp (-(q * (u n i : ℝ))) *
                    (X.generator w (Z i) - q * w (Z i)) *
                      ((u n (i + 1) : ℝ) - (u n i : ℝ))| =
                    |(Real.exp (-(q * (u n i : ℝ))) *
                       ((u n (i + 1) : ℝ) - (u n i : ℝ))) *
                       (X.generator w (Z i) - q * w (Z i))| := by
                        congr 1
                        ring
                _ = _ := by rw [abs_mul, abs_of_nonneg hWeight]
      _ ≤ _ := hScaled
  · dsimp only [Z] at hm
    simp only [if_neg hm, Real.norm_eq_abs, abs_zero]
    exact mul_nonneg hWeight (mul_nonneg hCoeff hR)
