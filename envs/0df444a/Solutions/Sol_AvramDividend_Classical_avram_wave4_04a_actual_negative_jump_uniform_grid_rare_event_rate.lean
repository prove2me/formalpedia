-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_negative_jump_uniform_grid_rare_event_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T23:57:22.266921+00:00
-- url     : https://prove2.me/submissions/9429f9f3-cb01-42a4-b3ad-5896649ab267

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! The source negative-activity Bernoulli rare-event rate on uniform grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      (n : ℝ) *
        (1 - Real.exp (-(((T : ℝ) *
          (X.ν (Iio (0 : ℝ))).toReal) / (n : ℝ)))))
      atTop (𝓝 ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  let c : ℝ := (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal
  change Tendsto (fun n : ℕ => (n : ℝ) *
    (1 - Real.exp (-(c / (n : ℝ))))) atTop (𝓝 c)
  by_cases hc : c = 0
  · simpa [hc] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)))
  · have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹)
        atTop (𝓝 (0 : ℝ)) := by
      exact tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto
          (fun n : ℕ => (n : ℝ)) atTop atTop)
    have hArg : Tendsto (fun n : ℕ => -(c / (n : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
      have hMul : Tendsto (fun n : ℕ => c * (n : ℝ)⁻¹)
          atTop (𝓝 (c * (0 : ℝ))) :=
        tendsto_const_nhds.mul hInv
      simpa [div_eq_mul_inv] using hMul.neg
    have hNZ : ∀ᶠ n : ℕ in atTop, -(c / (n : ℝ)) ≠ 0 := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      exact neg_ne_zero.mpr (div_ne_zero hc hn0)
    have hArg' : Tendsto (fun n : ℕ => -(c / (n : ℝ)))
        atTop (𝓝[≠] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hArg, hNZ⟩
    have hSlope : Tendsto
        (fun x : ℝ => x⁻¹ * (Real.exp x - 1))
        (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      simpa only [zero_add, Real.exp_zero, smul_eq_mul] using
        (Real.hasDerivAt_exp 0).tendsto_slope_zero
    have hRatio : Tendsto
        (fun n : ℕ => (-(c / (n : ℝ)))⁻¹ *
          (Real.exp (-(c / (n : ℝ))) - 1))
        atTop (𝓝 (1 : ℝ)) := hSlope.comp hArg'
    have hScaled : Tendsto
        (fun n : ℕ => c * ((-(c / (n : ℝ)))⁻¹ *
          (Real.exp (-(c / (n : ℝ))) - 1)))
        atTop (𝓝 c) := by
      simpa using (tendsto_const_nhds.mul hRatio)
    have hEq : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * (1 - Real.exp (-(c / (n : ℝ)))) =
          c * ((-(c / (n : ℝ)))⁻¹ *
            (Real.exp (-(c / (n : ℝ))) - 1)) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp [hc, hn0]
      ring
    apply hScaled.congr'
    filter_upwards [hEq] with n hn
    exact hn.symm
