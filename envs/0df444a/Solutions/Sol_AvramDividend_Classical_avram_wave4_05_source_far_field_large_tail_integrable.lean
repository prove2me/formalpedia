-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_far_field_large_tail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:55:47.668087+00:00
-- url     : https://prove2.me/submissions/10644aef-c206-4d19-9a08-eb87615ae80f

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The unsubtracted large negative-jump difference is genuinely ν-integrable,
including arbitrarily severe ruin-crossing jumps, without a first moment assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    IntegrableOn (fun y : ℝ => vcstar W (x + y) - vcstar W x)
      (Iic (-1 : ℝ)) X.ν := by
  have hx : (cstar W).toReal < x := by linarith
  have hdom : X.GeneratorIntegrable (vcstar W) x :=
    vcstar_generatorIntegrable_strictly_above_real_cstar
      X q W hW x hx
  have hs : Iic (-1 : ℝ) ⊆ Iio (0 : ℝ) := by
    intro y hy
    change y ≤ -1 at hy
    change y < 0
    linarith
  have hsub : IntegrableOn
      (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x)
      (Iic (-1 : ℝ)) X.ν := hdom.mono_set hs
  have hon : Set.EqOn
      (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x)
      (fun y : ℝ => vcstar W (x + y) - vcstar W x)
      (Iic (-1 : ℝ)) := by
    intro y hy
    have hylarge : y ≤ -1 := hy
    have hyneg : y < 0 := by linarith
    rw [avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel
      W x y hfar hyneg, if_pos hylarge]
  exact (integrableOn_congr_fun hon measurableSet_Iic).mp hsub
