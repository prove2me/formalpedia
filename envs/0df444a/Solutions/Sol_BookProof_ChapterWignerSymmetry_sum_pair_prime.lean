-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.sum_pair_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:55:07.013205+00:00
-- url     : https://prove2.me/submissions/c72c03d8-b20a-4424-97bf-944e05fed8ed

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.sum_pair'
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Theorems.Thm_BookProof_ChapterWignerSymmetry_sum_supported
open BookProof.ChapterWignerSymmetry



open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {T : E → E}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
theorem solution {o i : ι} (hi : i ≠ o) {f : ι → ℂ} (hf : ∀ k, k ≠ o → k ≠ i → f k = 0)
    (g : ι → ℂ) : ∑ k, g k * f k = g o * f o + g i * f i := by

  classical
  rw [sum_supported (s := ({o, i} : Finset ι)) (fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      exact hf k hk.1 hk.2) g]
  rw [Finset.sum_pair (Ne.symm hi)]
