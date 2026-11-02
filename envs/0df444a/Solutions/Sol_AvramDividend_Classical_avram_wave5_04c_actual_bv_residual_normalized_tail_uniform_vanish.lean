-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:41:34.519027+00:00
-- url     : https://prove2.me/submissions/9010cad3-afb1-4bfb-989b-70ed523cd471

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_integrable_real_truncated_first_moment_tail_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_le_two_terminal_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
       ∀ h : ℝ≥0, 0 < h → h ≤ (1 / 2 : ℝ≥0) →
       (h : ℝ)⁻¹ * (∫ ω, if (n : ℝ) < (h : ℝ) * X.drift - X.X h ω
          then (h : ℝ) * X.drift - X.X h ω else 0 ∂P) < ε := by
  let R : Ω → ℝ := fun ω => (1 : ℝ) * X.drift - X.X 1 ω
  have hRI : Integrable R P := by
    simpa only [R, NNReal.coe_one] using
      avram_wave5_04c_actual_bv_residual_integrable_upto_one
        X hX hBV 1 le_rfl
  have hRM : Measurable R :=
    measurable_const.sub ((X.adapted 1).mono (𝓕.le _) le_rfl)
  have hlim : Tendsto
      (fun n : ℕ => ∫ ω, if (n : ℝ) < R ω then R ω else 0 ∂P)
      atTop (nhds 0) :=
    avram_wave5_04c_integrable_real_truncated_first_moment_tail_tendsto_zero
      R hRM hRI
  have hlim2 : Tendsto
      (fun n : ℕ => 2 * (∫ ω, if (n : ℝ) < R ω then R ω else 0 ∂P))
      atTop (nhds 0) := by
    convert tendsto_const_nhds.mul hlim using 1 <;> simp
  intro ε hε
  filter_upwards [hlim2.eventually (eventually_lt_nhds hε)] with n hn
  intro h hpos hhalf
  have hbound :=
    avram_wave5_04c_actual_bv_residual_normalized_tail_le_two_terminal_tail
      X hX hBV h hpos hhalf (n : ℝ)
  exact lt_of_le_of_lt hbound (by simpa only [R, NNReal.coe_one] using hn)
