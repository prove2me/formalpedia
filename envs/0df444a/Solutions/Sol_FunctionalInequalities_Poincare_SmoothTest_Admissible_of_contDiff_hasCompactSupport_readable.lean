-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:56.16181+00:00
-- url     : https://prove2.me/submissions/7736128a-2d71-49c3-9e51-bf9c4c6f42e2

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
section Cutoff
variable [FiniteDimensional ℝ E]
/-- A `C^∞` function with compact support is an admissible test for every finite measure. -/
theorem solution {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : FunctionalInequalities.Poincare.SmoothTest.Admissible μ f := by
    refine
      { smooth' := hf
        memLp_two := ?_
        energy_integrable := ?_ }
    · obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf.continuous
      exact
        MemLp.of_bound hf.continuous.aestronglyMeasurable C
          (Filter.Eventually.of_forall hC)
    · have hgrad : Continuous (gradient f) := by
        change
          Continuous
            (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
        exact
          (InnerProductSpace.toDual ℝ E).symm.continuous.comp
            (hf.continuous_fderiv (by simp))
      have henergy : Continuous (fun x => ‖gradient f x‖ ^ 2) :=
        hgrad.norm.pow 2
      have hfd : HasCompactSupport (fun x => fderiv ℝ f x) :=
        hc.fderiv ℝ
      have hsub :
          Function.support (fun x => ‖gradient f x‖ ^ 2) ⊆
            Function.support (fun x => fderiv ℝ f x) := by
        intro x hx hfx
        apply hx
        simp [gradient, hfx]
      exact henergy.integrable_of_hasCompactSupport (hfd.mono hsub)
