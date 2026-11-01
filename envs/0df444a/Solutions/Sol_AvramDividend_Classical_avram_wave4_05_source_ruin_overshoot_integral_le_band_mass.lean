-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_ruin_overshoot_integral_le_band_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:22:30.274221+00:00
-- url     : https://prove2.me/submissions/9a6b5585-2255-4d03-8796-67facc879c25

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_overshoot_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The positive small-ruin compensator has an explicit finite-band
Levy-mass upper bound, with no assumption on the first Levy moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν < ⊤) :
    (∫ y in Ioo (-1 : ℝ) (-x), max 0 (-vcstar W x - y) ∂X.ν) ≤
      (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) := by
  let s : Set ℝ := Ioo (-1 : ℝ) (-x)
  let C : ℝ := max 0 (1 - vcstar W x)
  have hsub : s ⊆ Iic (-x) := by
    intro y hy
    exact le_of_lt hy.2
  have hfin : X.ν s < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub)
      (negative_jump_truncation_measure_finite X.ν hνint x hx)
  have hover : Integrable (s.indicator
      (fun y : ℝ => max 0 (-vcstar W x - y))) X.ν :=
    avram_wave4_05_source_ruin_overshoot_integrable X W x hx hνint
  have hOn : IntegrableOn
      (fun y : ℝ => max 0 (-vcstar W x - y)) s X.ν :=
    (integrable_indicator_iff measurableSet_Ioo).mp hover
  have hC : 0 ≤ C := le_max_left _ _
  have hconst : IntegrableOn (fun _ : ℝ => C) s X.ν := by
    refine IntegrableOn.of_bound hfin (by fun_prop) C ?_
    exact Filter.Eventually.of_forall (fun y => by
      simp [Real.norm_eq_abs, abs_of_nonneg hC])
  have hcomp :
      (∫ y in s, max 0 (-vcstar W x - y) ∂X.ν) ≤
        ∫ y in s, C ∂X.ν := by
    apply setIntegral_mono_on hOn hconst measurableSet_Ioo
    intro y hy
    exact max_le_max_left 0 (by linarith [hy.1])
  calc
    (∫ y in Ioo (-1 : ℝ) (-x), max 0 (-vcstar W x - y) ∂X.ν) ≤
        ∫ y in s, C ∂X.ν := hcomp
    _ = (X.ν).real s * C := by simp [setIntegral_const, mul_comm]
    _ = (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) := rfl
