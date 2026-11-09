-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_small13_original_BV_positive_shift_generator_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:34:20.692839+00:00
-- url     : https://prove2.me/submissions/c490a977-2aa8-4822-a43c-8269f3ecd83c

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Translate the original BV source generator into the strictly positive
reserve region. The original negative-jump measure and filtration are unchanged. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      X.GeneratorIntegrable w z ∧ X.generator w z - q * w z ≤ 0)
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (δ y : ℝ) (hδ : 0 < δ) (hy : 0 ≤ y)
    (hcap : ENNReal.ofReal (y + δ) < C) :
    X.GeneratorIntegrable (fun v : ℝ => w (v + δ)) y ∧
      X.generator (fun v : ℝ => w (v + δ)) y - q * w (y + δ) ≤ 0 ∧
      1 ≤ deriv (fun v : ℝ => w (v + δ)) y := by
  classical
  have hpositive : 0 < y + δ := by linarith
  obtain ⟨hSourceInt, hSourceSign⟩ := hw_gen (y + δ) hpositive hcap
  have hDeriv : deriv (fun v : ℝ => w (v + δ)) y = deriv w (y + δ) := by
    simp only [deriv_comp_add_const]
  have hKernel (z : ℝ) :
      SpectrallyNegativeLevy.generatorIntegrand (fun v : ℝ => w (v + δ)) y z =
        SpectrallyNegativeLevy.generatorIntegrand w (y + δ) z := by
    unfold SpectrallyNegativeLevy.generatorIntegrand
    dsimp only
    rw [hDeriv]
    have hAdd : y + z + δ = y + δ + z := by ring
    rw [hAdd]
  have hKernelFun : SpectrallyNegativeLevy.generatorIntegrand
      (fun v : ℝ => w (v + δ)) y =
      SpectrallyNegativeLevy.generatorIntegrand w (y + δ) := funext hKernel
  have hInt : X.GeneratorIntegrable (fun v : ℝ => w (v + δ)) y := by
    change IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand
        (fun v : ℝ => w (v + δ)) y)
      (Iio (0 : ℝ)) X.ν
    rw [hKernelFun]
    exact hSourceInt
  have hSigma : X.σ = 0 := hBV.1
  have hGenerator : X.generator (fun v : ℝ => w (v + δ)) y =
      X.generator w (y + δ) := by
    simp [SpectrallyNegativeLevy.generator, hSigma, hDeriv, hKernelFun]
  refine ⟨hInt, ?_, ?_⟩
  · rw [hGenerator]
    exact hSourceSign
  · rw [hDeriv]
    exact hw_grad (y + δ) hpositive hcap
