-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.sum_pairCoord
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:05:57.716522+00:00
-- url     : https://prove2.me/submissions/09289ab5-ec5e-4846-800c-fff7814d02a4

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.sum_pairCoord
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
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

set_option maxHeartbeats 1000000 in
theorem solution (b : OrthonormalBasis ι ℂ E) {o i : ι} (hi : i ≠ o) :
    ∑ j, pairCoord o i j • b j = b o + b i := by

  have hz : ∀ j ∈ (Finset.univ : Finset ι), j ∉ ({o, i} : Finset ι) →
      pairCoord o i j • b j = 0 := by
    intro j _ hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [pairCoord, hj.1, hj.2]
  rw [← Finset.sum_subset (Finset.subset_univ _) hz, Finset.sum_pair (Ne.symm hi)]
  simp [pairCoord, hi]
