-- Prove2me | solution 1 for BookProof.CarlemanSimplex.rcm_shiftm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:09:03.801771+00:00
-- url     : https://prove2.me/submissions/3ffc0964-be0c-4a3d-b246-767dabed93e8

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.rcm_shiftm
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_shiftm_apply_self
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
theorem solution {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) :
    rcm (shiftm a i j) j i = rcm a i j := by

  classical
  have h2 : ((shiftm a i j - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) = a j - 1 := by
    simp only [shiftm, Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have e1 : (((shiftm a i j) i : ℕ) : ℝ)
      = (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℝ) + 1 := by
    rw [shiftm_apply_self]
    push_cast
    ring
  have e2 : ((((shiftm a i j - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ)) + 1
      = ((a j : ℕ) : ℝ) := by
    rw [h2]
    have h1 : (1 : ℕ) ≤ a j := h
    push_cast [Nat.cast_sub h1]
    ring
  rw [rcm, rcm, e1, e2, mul_comm]
