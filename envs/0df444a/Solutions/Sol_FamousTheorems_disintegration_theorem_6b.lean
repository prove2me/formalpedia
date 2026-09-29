-- Prove2me | solution 1 for FamousTheorems.disintegration_theorem_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:50:20.384031+00:00
-- url     : https://prove2.me/submissions/9f6a7d79-9578-43fd-9ce9-4c7ef4af8e26

import Mathlib

theorem solution {α Ω : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]
    (ρ : MeasureTheory.Measure (α × Ω)) [MeasureTheory.IsFiniteMeasure ρ] :
    ∃ κ : ProbabilityTheory.Kernel α Ω, ProbabilityTheory.IsMarkovKernel κ ∧ ρ.fst.compProd κ = ρ :=
  ⟨ρ.condKernel, inferInstance, MeasureTheory.Measure.disintegrate ρ ρ.condKernel⟩
