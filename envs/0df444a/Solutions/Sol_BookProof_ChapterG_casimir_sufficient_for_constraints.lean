-- Prove2me | solution 1 for BookProof.ChapterG.casimir_sufficient_for_constraints
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:20:22.321346+00:00
-- url     : https://prove2.me/submissions/8da1a32f-e7b8-430e-bb02-0dce8f9eb591

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.casimir_sufficient_for_constraints
import Mathlib
import Definitions.Def_ChapterG
open MeasureTheory
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]
variable {A : Type*} [Ring A]
variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {ν : Measure β}
  {p : ENNReal} [Fact (1 ≤ p)]

set_option maxHeartbeats 1000000 in
theorem solution {X Y : Type*} (π : X → Y)
    (h : IsUnconstrainedGaugeFixing π) :
    gaugeInvariantSubalgebra ℝ π ≠ ⊤ := by

  rcases h with ⟨g, hg, f, hf⟩
  exfalso
  have h_contra : (f : X → ℝ) ∘ g = (f : X → ℝ) := by
    have h_mem : ∀ x, (f : X → ℝ) (g x) = (f : X → ℝ) x := f.property g hg
    ext x; exact h_mem x
  exact hf h_contra
