-- Prove2me | solution 1 for AvramDividend.Classical.kernel_cutoff_finite_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:34:52.616927+00:00
-- url     : https://prove2.me/submissions/f8a78363-3757-410b-963a-29ebd1f14def

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.GiryMonad

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    (S : Set Ω) (hS : MeasurableSet S)
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hBound : ∀ ω : Ω, ω ∈ S → (κ ω) Set.univ ≤ C) :
    ∃ κCut : ProbabilityTheory.Kernel Ω ℝ,
      (∀ ω : Ω, κCut ω =
        if ω ∈ S then κ ω else (0 : MeasureTheory.Measure ℝ)) ∧
      ProbabilityTheory.IsFiniteKernel κCut := by
  have hκ : Measurable (fun ω : Ω => κ ω) :=
    Measure.measurable_measure.mpr (fun s hs => κ.measurable_coe hs)
  have hcut : Measurable (fun ω : Ω =>
      if ω ∈ S then κ ω else (0 : Measure ℝ)) :=
    Measurable.ite hS hκ measurable_const
  let κCut : ProbabilityTheory.Kernel Ω ℝ :=
    ProbabilityTheory.Kernel.mk
      (fun ω : Ω => if ω ∈ S then κ ω else (0 : Measure ℝ)) hcut
  refine ⟨κCut, ?_, ?_⟩
  · intro ω
    rfl
  · refine ⟨⟨C, hC, ?_⟩⟩
    intro ω
    change (if ω ∈ S then κ ω else (0 : Measure ℝ)) Set.univ ≤ C
    by_cases hω : ω ∈ S
    · simpa [hω] using hBound ω hω
    · simp [hω]
