-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_measurable_random_joint_indicator_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:22:43.510297+00:00
-- url     : https://prove2.me/submissions/4a087fa4-215d-4402-a021-e6d2d8d22e5c

import Mathlib
import Mathlib.Probability.Kernel.MeasurableLIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    [ProbabilityTheory.IsSFiniteKernel κ]
    (S : Set (ℝ × Ω)) (hS : MeasurableSet S)
    (f : ℝ × Ω → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω : Ω => ∫⁻ t, if (t, ω) ∈ S then f (t, ω) else 0 ∂κ ω) := by
  classical
  have hS' : MeasurableSet {p : ℝ × Ω | p ∈ S} := hS
  have hJoint : Measurable (fun p : ℝ × Ω => if p ∈ S then f p else 0) :=
    Measurable.ite (p := fun p => p ∈ S) hS' hf measurable_const
  have hUncurry : Measurable (Function.uncurry
      (fun t ω => if (t, ω) ∈ S then f (t, ω) else 0)) := by
    convert hJoint using 1
    funext p
    rcases p with ⟨t, ω⟩
    rfl
  exact Measurable.lintegral_kernel_prod_left
    (κ := κ) (f := fun t ω => if (t, ω) ∈ S then f (t, ω) else 0)
    hUncurry
