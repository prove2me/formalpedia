-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys56_uniform_finite_random_integral_strongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:20:49.141385+00:00
-- url     : https://prove2.me/submissions/c772505c-9611-4e1e-bbbd-8446ba94f0e2

import Mathlib.Probability.Kernel.MeasurableIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- A uniformly finite measurable random measure integrates jointly measurable rewards measurably. -/
theorem solution
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (M : Ω → Measure α)
    (hM : ∀ S : Set α, MeasurableSet S →
      Measurable (fun ω : Ω => M ω S))
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hMass : ∀ ω : Ω, M ω Set.univ ≤ C)
    (f : Ω × α → ℝ) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun ω : Ω => ∫ p, f (ω, p) ∂M ω) := by
  have hm : Measurable M := Measure.measurable_of_measurable_coe M hM
  let κ : ProbabilityTheory.Kernel Ω α := ⟨M, hm⟩
  haveI : ProbabilityTheory.IsFiniteKernel κ :=
    ⟨⟨C, hC, by intro ω; exact hMass ω⟩⟩
  change StronglyMeasurable (fun ω : Ω => ∫ p, f (ω, p) ∂κ ω)
  exact MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'
    (κ := κ) hf
