-- Prove2me | solution 1 for BookProof.CarlemanSimplex.deg_shiftm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:07:14.258902+00:00
-- url     : https://prove2.me/submissions/7d7699ff-3d61-4a03-98a9-538f4e94c6c1

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.deg_shiftm
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_deg_add
import Theorems.Thm_BookProof_CarlemanSimplex_deg_single
import Theorems.Thm_BookProof_CarlemanSimplex_deg_tsub_of_le
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) : deg (shiftm a i j) = deg a := by

  have hle : Finsupp.single j 1 ≤ a := by
    rw [Finsupp.le_def]
    intro k
    by_cases hk : k = j
    · subst hk; simpa using h
    · simp [Ne.symm hk]
  rw [shiftm, deg_add, deg_single, ← deg_tsub_of_le hle, deg_single]
