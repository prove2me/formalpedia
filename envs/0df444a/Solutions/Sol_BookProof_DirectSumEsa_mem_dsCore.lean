-- Prove2me | solution 1 for BookProof.DirectSumEsa.mem_dsCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:49:39.437+00:00
-- url     : https://prove2.me/submissions/1e7431aa-b2a7-40fe-b1d1-36b6ad54c8eb

-- Generated from ChapterDirectSumEsa.lean — solution of BookProof.DirectSumEsa.mem_dsCore
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
open BookProof.DirectSumEsa



open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

set_option maxHeartbeats 1000000 in
theorem solution {D : ∀ i, Submodule ℂ (G i)} {f : lp G 2} :
    f ∈ dsCore D ↔ {i | (f : ∀ i, G i) i ≠ 0}.Finite ∧ ∀ i, (f : ∀ i, G i) i ∈ D i := Iff.rfl
