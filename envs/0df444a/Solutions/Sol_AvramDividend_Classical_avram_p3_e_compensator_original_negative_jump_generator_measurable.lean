-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_negative_jump_generator_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:53:16.877193+00:00
-- url     : https://prove2.me/submissions/c95a60a4-7b29-4885-892e-236bf5ca950d

import Mathlib
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Measurability of the exact original Lévy negative-jump generator. -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕)
(hSigma : SigmaFinite X.ν)
(w : ℝ → ℝ) (hwMeas : Measurable w) :
Measurable (fun y : ℝ =>
  ∫ z in Set.Iio (0 : ℝ), w (y + z) - w y ∂X.ν) := by
  letI : SigmaFinite X.ν := hSigma
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : SFinite μ := inferInstance
  let κ : ProbabilityTheory.Kernel ℝ ℝ :=
    ProbabilityTheory.Kernel.const ℝ μ
  letI : ProbabilityTheory.IsSFiniteKernel κ := by
    dsimp [κ]
    infer_instance
  have hF : Measurable (fun p : ℝ × ℝ =>
      w (p.1 + p.2) - w p.1) :=
    (hwMeas.comp (measurable_fst.add measurable_snd)).sub
      (hwMeas.comp measurable_fst)
  have hInt : StronglyMeasurable (fun y : ℝ =>
      ∫ z : ℝ, w (y + z) - w y ∂κ y) :=
    hF.stronglyMeasurable.integral_kernel_prod_right'
  have hEq :
      (fun y : ℝ => ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) =
      (fun y : ℝ => ∫ z : ℝ, w (y + z) - w y ∂κ y) := by
    funext y
    rfl
  rw [hEq]
  exact hInt.measurable
