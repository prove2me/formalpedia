-- Prove2me | solution 1 for BookProof.ChapterG.gaugeInvariant_constant_on_fibers
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:22:25.327492+00:00
-- url     : https://prove2.me/submissions/e0170875-2737-4e15-bde9-b88914678e83

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.gaugeInvariant_constant_on_fibers
import Mathlib
import Definitions.Def_ChapterG
import Theorems.Thm_BookProof_ChapterG_swap_mem_gaugeGroup
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
theorem solution {X Y : Type*}
    (π : X → Y) (f : X → ℝ) (hf : ∀ g ∈ gaugeGroup π, ∀ x, f (g x) = f x)
    (x y : X) (h : π x = π y) : f x = f y := by

  classical
    have hswap : Equiv.swap x y ∈ gaugeGroup π := swap_mem_gaugeGroup h
    have h_eq := hf (Equiv.swap x y) hswap x
    simpa [Equiv.swap_apply_left] using h_eq.symm
