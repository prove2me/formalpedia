-- Prove2me | solution 1 for BookProof.CarlemanSimplex.shiftm_shiftm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:43:16.362291+00:00
-- url     : https://prove2.me/submissions/4ab6972e-adc6-485d-be3d-d55b8f6df592

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.shiftm_shiftm
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_tsub_add_cancel_of_le_prime
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

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
theorem solution {a : Fin d →₀ ℕ} {i j : Fin d} (h : 1 ≤ a j) :
    shiftm (shiftm a i j) j i = a := by

  have hle : Finsupp.single j 1 ≤ a := by
    rw [Finsupp.le_def]
    intro k
    by_cases hk : k = j
    · subst hk; simpa using h
    · simp [Ne.symm hk]
  rw [shiftm, shiftm, add_tsub_cancel_right, tsub_cancel_le hle]
