-- Prove2me | solution 1 for BookProof.CarlemanSimplex.deg_tsub_of_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:43:07.620207+00:00
-- url     : https://prove2.me/submissions/d5ecc567-07a6-45ea-b69b-86640ed02488

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.deg_tsub_of_le
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_deg_add
import Theorems.Thm_BookProof_CarlemanSimplex_tsub_add_cancel_of_le_prime
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

/-- Cancellation of a truncated subtraction below a multi-index.  The platform's
published `ChapterCarlemanSimplex` bundle predates this lemma, and a solution may
not rely on unpublished declarations, so it is proved locally (§5a embed helper). -/
private theorem tsub_cancel_le {P a : Fin d →₀ ℕ} (h : P ≤ a) : a - P + P = a := by
  ext j
  have hj : P j ≤ a j := by
    have := h
    rw [Finsupp.le_def] at this
    exact this j
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  omega

set_option maxHeartbeats 1000000 in
theorem solution {P a : Fin d →₀ ℕ} (h : P ≤ a) : deg (a - P) + deg P = deg a := by

  rw [← deg_add, tsub_cancel_le h]
