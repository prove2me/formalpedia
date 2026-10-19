-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_far_field_generator_residual_nonpos_of_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:20:35.536842+00:00
-- url     : https://prove2.me/submissions/8d6ae144-9962-4225-9c80-1ae71dbc425d

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrier_generatorIntegrand_zero_small_negative_jump_above
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_above_eq_drift_add_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hmono : Monotone (vcstar W))
    (x : ℝ)
    (hfar : (cstar W).toReal + 1 ≤ x)
    (hbound : X.c ≤ q * vcstar W x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤ 0 := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hx : a < x := by dsimp [a]; linarith
  have hjump : (∫ y in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) ≤ 0 := by
    apply setIntegral_nonpos measurableSet_Iio
    intro y hy
    have hyneg : y < 0 := hy
    by_cases hlarge : y ≤ -1
    · have hnot : y ∉ Ioo (-1 : ℝ) 1 := by
        intro hmem
        exact (not_lt_of_ge hlarge) hmem.1
      have hxy : x + y ≤ x := by linarith
      have hm : vcstar W (x + y) ≤ vcstar W x := hmono hxy
      unfold SpectrallyNegativeLevy.generatorIntegrand
      simp [Set.indicator_of_notMem hnot]
      linarith
    · have hy1 : -1 < y := lt_of_not_ge hlarge
      have hxy : a < x + y := by dsimp [a] at *; linarith
      have hz :
          SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y = 0 := by
        change SpectrallyNegativeLevy.generatorIntegrand
          (barrierValue W a) x y = 0
        exact barrier_generatorIntegrand_zero_small_negative_jump_above
          W a x y ha hx hxy hy1 hyneg
      exact le_of_eq hz
  refine ⟨vcstar_generatorIntegrable_strictly_above_real_cstar
      X q W hW x hx, ?_⟩
  rw [vcstar_generator_above_eq_drift_add_jump X W x hx]
  linarith