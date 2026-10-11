-- Prove2me | solution 1 for BookProof.SymmetryEntropy.isDeterministicCol_iff_entropy_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:43.411255+00:00
-- url     : https://prove2.me/submissions/9cad3408-99cd-4cb3-a641-317cc9c150e8

-- Generated from ChapterSymmetryEntropy.lean — solution of BookProof.SymmetryEntropy.isDeterministicCol_iff_entropy_eq_zero
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
import Theorems.Thm_BookProof_SymmetryEntropy_entropy_eq_zero_iff
import Theorems.Thm_BookProof_SymmetryEntropy_bornCol_nonneg
import Theorems.Thm_BookProof_SymmetryEntropy_bornCol_le_one
import Theorems.Thm_BookProof_SymmetryEntropy_exists_eq_one_of_isDeterministicCol
import Theorems.Thm_BookProof_SymmetryEntropy_isDeterministicCol_of_entropy_eq_zero
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterIrreversible
import Definitions.Def_ChapterReconstruct
open BookProof.SymmetryEntropy




open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) :
    IsDeterministicCol U a ↔ entropy (bornCol U a) = 0 := by

  constructor
  · intro hdet
    obtain ⟨k, hk1, hk0⟩ := exists_eq_one_of_isDeterministicCol hcol hdet
    refine (entropy_eq_zero_iff (bornCol_nonneg U a) (bornCol_le_one hcol)).mpr fun l => ?_
    by_cases hl : l = k
    · exact Or.inr (hl ▸ hk1)
    · exact Or.inl (hk0 l hl)
  · exact isDeterministicCol_of_entropy_eq_zero hcol
