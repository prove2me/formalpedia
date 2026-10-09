-- Prove2me | solution 1 for BookProof.DirectSumEdge.mem_supportFinset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:43:02.421717+00:00
-- url     : https://prove2.me/submissions/13150041-4c36-40bb-acde-bf32ef81de94

-- Generated from ChapterDirectSumEdge.lean — solution of BookProof.DirectSumEdge.mem_supportFinset
import Mathlib
import Definitions.Def_ChapterDirectSumEdge
open BookProof.DirectSumEdge




open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

set_option maxHeartbeats 1000000 in
theorem solution {x : dsCore D} {i : ι} :
    i ∈ supportFinset x ↔ ((x : lp G 2) : ∀ i, G i) i ≠ 0 := x.2.1.mem_toFinset
