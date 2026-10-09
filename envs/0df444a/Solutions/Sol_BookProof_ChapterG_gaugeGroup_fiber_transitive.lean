-- Prove2me | solution 1 for BookProof.ChapterG.gaugeGroup_fiber_transitive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:20:06.762432+00:00
-- url     : https://prove2.me/submissions/114114f1-9540-4891-92d7-c1d771ecdc80

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.gaugeGroup_fiber_transitive
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
    (x₁ x₂ : X) (h : π x₁ = π x₂) : ∃ g ∈ gaugeGroup π, g x₁ = x₂ := by

  classical
    let σ : Equiv.Perm X := Equiv.swap x₁ x₂
    have hσ : σ ∈ gaugeGroup π := by
      rw [mem_gaugeGroup]
      intro x
      dsimp [σ]
      rw [Equiv.swap_apply_def]
      split_ifs with hx₁ hx₂
      · rw [hx₁, h]
      · rw [hx₂, ← h]
      · rfl
    exact ⟨σ, hσ, by
      dsimp [σ]
      exact Equiv.swap_apply_left x₁ x₂⟩
