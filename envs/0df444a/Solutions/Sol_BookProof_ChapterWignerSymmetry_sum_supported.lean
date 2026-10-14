-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.sum_supported
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:54:52.437527+00:00
-- url     : https://prove2.me/submissions/aa3406ae-4739-496b-aaf5-3809cf7572c5

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.sum_supported
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry



open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {T : E → E}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
theorem solution {s : Finset ι} {f : ι → ℂ} (hf : ∀ k, k ∉ s → f k = 0) (g : ι → ℂ) :
    ∑ k, g k * f k = ∑ k ∈ s, g k * f k := (Finset.sum_subset (Finset.subset_univ s) (fun k _ hk => by rw [hf k hk, mul_zero])).symm
