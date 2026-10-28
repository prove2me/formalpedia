-- Prove2me | solution 1 for AvramDividend.Classical.generator_vcstar_eq_zero_of_zero_scale_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:07:40.584475+00:00
-- url     : https://prove2.me/submissions/ffe0fe5c-7470-4f79-a3ed-74b7903615cd

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_eq_of_agree_below
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

private theorem divE_zero_of_divE_one_zero (d : EReal)
    (h : divE (1 : ℝ) d = 0) (r : ℝ) : divE r d = 0 := by
  by_cases htop : d = ⊤
  · simp [divE, htop]
  · have hden : d.toReal = 0 := by
      by_contra hne
      have hdiv : (1 : ℝ) / d.toReal = 0 := by
        simpa [divE, htop] using h
      exact (div_ne_zero (by norm_num) hne) hdiv
    simp [divE, htop, hden]

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hsupport : ∀ z : ℝ, z < 0 → W z = 0)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by
  have hvanish : ∀ z : ℝ, z < (cstar W).toReal → vcstar W z = 0 := by
    intro z hz
    rw [vcstar_eq_scaledW_le_cstar_of_support W hsupport z (le_of_lt hz)]
    exact divE_zero_of_divE_one_zero
      (scaleDeriv W (cstar W).toReal) hk (W z)
  intro x hx
  have hlocal := generator_eq_of_agree_below X
    (vcstar W) (fun _ : ℝ => (0 : ℝ))
    (cstar W).toReal x hx.2 hvanish
  have hzeroInt : X.GeneratorIntegrable (fun _ : ℝ => (0 : ℝ)) x := by
    have hpoint :
        (fun y : ℝ => SpectrallyNegativeLevy.generatorIntegrand
          (fun _ : ℝ => (0 : ℝ)) x y) = (fun _ : ℝ => 0) := by
      funext y
      unfold SpectrallyNegativeLevy.generatorIntegrand
      simp
    change Integrable
      (fun y : ℝ => SpectrallyNegativeLevy.generatorIntegrand
        (fun _ : ℝ => (0 : ℝ)) x y)
      (X.ν.restrict (Iio (0 : ℝ)))
    rw [hpoint]
    simp
  have hzeroGen : X.generator (fun _ : ℝ => (0 : ℝ)) x = 0 := by
    simp [SpectrallyNegativeLevy.generator,
      SpectrallyNegativeLevy.generatorIntegrand]
  refine ⟨hlocal.1.mpr hzeroInt, ?_⟩
  rw [hlocal.2, hvanish x hx.2, hzeroGen]
  ring
