-- Prove2me | solution 1 for AvramDividend.Classical.avram_b20_nostanding_finiteactivity_actual_jump_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:31:38.761367+00:00
-- url     : https://prove2.me/submissions/c6e7e11f-e82c-4c80-bd92-557977d22a64

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b20_nostanding_finiteactivity_integer_negative_jumps_equal_drift_deficit
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ n : ℕ,
      (∫ ω : Ω, Real.exp (-
        ((∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ (n : ℝ≥0) then
            ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
        Real.exp (-((n : ℝ) *
          (∫ y in Iio (0 : ℝ), (1 - Real.exp y) ∂X.ν))) := by
  intro n
  have hPath : ∀ᵐ ω ∂P,
      ((∑' (v : ℝ≥0), if 0 < v ∧ v ≤ (n : ℝ≥0) then
        ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) = (n : ℝ) * X.drift - X.X (n : ℝ≥0) ω := by
    filter_upwards
      [avram_b20_nostanding_finiteactivity_integer_negative_jumps_equal_drift_deficit
        X hBV hFinite] with ω hω
    exact hω n
  have hI : (∫ ω : Ω, Real.exp (-
      ((∑' (v : ℝ≥0), if 0 < v ∧ v ≤ (n : ℝ≥0) then
        ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P) =
      (∫ ω : Ω, Real.exp ((1 : ℝ) * X.X (n : ℝ≥0) ω) *
        Real.exp (-((n : ℝ) * X.drift * (1 : ℝ))) ∂P) := by
    apply integral_congr_ae
    filter_upwards [hPath] with ω hω
    rw [hω, ← Real.exp_add]
    congr 1
    ring
  exact hI.trans (by simpa only [one_mul, mul_one, NNReal.coe_natCast] using
    (bv_actual_levy_drift_normalised_laplace
      X hBV (n : ℝ≥0) (1 : ℝ) (by norm_num)))
