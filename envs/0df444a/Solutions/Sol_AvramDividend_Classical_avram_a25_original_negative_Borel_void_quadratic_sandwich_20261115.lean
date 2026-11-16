-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_negative_Borel_void_quadratic_sandwich_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T14:50:27.326221+00:00
-- url     : https://prove2.me/submissions/c4a0627f-1cd0-4a3e-ae59-1d5038422190

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_void_fixed_horizon_moment_sandwich_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original fixed-horizon first and second count moments squeeze the void slope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let rate : ℝ := (T : ℝ) * (X.ν B).toReal
    let q : ℕ → ℝ := fun n =>
      1 - (P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (T / (n : ℝ≥0)) ×ˢ B) = 0}).toReal
    ∀ᶠ n in (Filter.atTop : Filter ℕ),
      rate - (rate ^ 2 / 2) * (1 / ((n : ℕ) : ℝ)) ≤
          ((n : ℕ) : ℝ) * q n ∧
        ((n : ℕ) : ℝ) * q n ≤ rate := by
  dsimp only
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hFix :=
    avram_a25_original_negative_Borel_void_fixed_horizon_moment_sandwich_20261115
      X hFinite (T / (n : ℝ≥0)) B hB hNeg
  dsimp only at hFix
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hFix
  have hRate : ((T / (n : ℝ≥0) : ℝ≥0) : ℝ) *
      (X.ν B).toReal = ((T : ℝ) * (X.ν B).toReal) / (n : ℝ) := by
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    ring
  rw [hRate] at hFix
  rcases hFix with ⟨hLo, hHi⟩
  have hnNe : (n : ℝ) ≠ 0 := ne_of_gt hnR
  constructor
  · calc
      _ = (n : ℝ) * (
          (((T : ℝ) * (X.ν B).toReal) / (n : ℝ)) -
          ((((T : ℝ) * (X.ν B).toReal) / (n : ℝ)) ^ 2) / 2) := by
            field_simp
      _ ≤ (n : ℝ) * (1 - (P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (T / (n : ℝ≥0)) ×ˢ B) = 0}).toReal) :=
          mul_le_mul_of_nonneg_left hLo (le_of_lt hnR)
  · calc
      _ ≤ (n : ℝ) *
          (((T : ℝ) * (X.ν B).toReal) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hHi (le_of_lt hnR)
      _ = (T : ℝ) * (X.ν B).toReal := by field_simp
