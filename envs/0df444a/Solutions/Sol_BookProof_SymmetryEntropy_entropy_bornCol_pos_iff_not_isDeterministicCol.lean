-- Prove2me | solution 1 for BookProof.SymmetryEntropy.entropy_bornCol_pos_iff_not_isDeterministicCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:44.829003+00:00
-- url     : https://prove2.me/submissions/4c46fe2c-67f2-489c-a16a-165ef2d33d43

-- Generated from ChapterSymmetryEntropy.lean — solution of BookProof.SymmetryEntropy.entropy_bornCol_pos_iff_not_isDeterministicCol
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
import Theorems.Thm_BookProof_SymmetryEntropy_entropy_nonneg
import Theorems.Thm_BookProof_SymmetryEntropy_bornCol_nonneg
import Theorems.Thm_BookProof_SymmetryEntropy_bornCol_le_one
import Theorems.Thm_BookProof_SymmetryEntropy_isDeterministicCol_iff_entropy_eq_zero
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
    0 < entropy (bornCol U a) ↔ ¬ IsDeterministicCol U a := by

  have hnn : 0 ≤ entropy (bornCol U a) :=
    entropy_nonneg (bornCol_nonneg U a) (bornCol_le_one hcol)
  rw [isDeterministicCol_iff_entropy_eq_zero hcol]
  constructor
  · intro hpos hzero
    exact absurd hzero (ne_of_gt hpos)
  · intro hne
    exact lt_of_le_of_ne hnn (fun h => hne h.symm)
