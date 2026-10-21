-- Prove2me | solution 1 for AvramDividend.Classical.measurable_random_indicator_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:54:00.008615+00:00
-- url     : https://prove2.me/submissions/d2317398-130d-4433-99b6-81d09a8e9f99

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    [ProbabilityTheory.IsSFiniteKernel κ]
    (S : Set (ℝ × Ω)) (hS : MeasurableSet S)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    Measurable (fun ω : Ω =>
      ∫⁻ t, if (t, ω) ∈ S then w t else 0 ∂κ ω) := by
  have hf : Measurable (fun p : ℝ × Ω =>
      if p ∈ S then w p.1 else 0) := by
    exact Measurable.ite hS (hw.comp measurable_fst) measurable_const
  have heq :
      (Function.uncurry
        (fun (t : ℝ) (ω : Ω) => if (t, ω) ∈ S then w t else 0)) =
      (fun p : ℝ × Ω => if p ∈ S then w p.1 else 0) := by
    funext p
    rcases p with ⟨t, ω⟩
    rfl
  have hf' : Measurable (Function.uncurry
      (fun (t : ℝ) (ω : Ω) => if (t, ω) ∈ S then w t else 0)) := by
    rw [heq]
    exact hf
  exact Measurable.lintegral_kernel_prod_left
    (κ := κ)
    (f := fun (t : ℝ) (ω : Ω) =>
      if (t, ω) ∈ S then w t else 0)
    hf'
