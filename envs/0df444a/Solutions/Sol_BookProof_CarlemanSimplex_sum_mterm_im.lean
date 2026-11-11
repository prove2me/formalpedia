-- Prove2me | solution 1 for BookProof.CarlemanSimplex.sum_mterm_im
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:09:18.542206+00:00
-- url     : https://prove2.me/submissions/bc5e40bc-1991-4863-a5ac-513a5561895f

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.sum_mterm_im
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_sum_mterm_conj
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
theorem solution {M : Fin d → Fin d → ℂ} (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j))
    (N : ℕ) : (∑ i, ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j).im = 0 := by

  classical
  set S : ℂ := ∑ i, ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j with hS
  have hconj : (starRingEnd ℂ) S = S := by
    rw [hS, map_sum]
    have h1 : ∀ i : Fin d, (starRingEnd ℂ) (∑ j, ∑ a ∈ simplexF d N, mterm u M a i j)
        = ∑ j, ∑ b ∈ simplexF d N, mterm u M b j i := by
      intro i
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => sum_mterm_conj hM N i j
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    exact Finset.sum_comm
  have := Complex.conj_eq_iff_im.mp hconj
  exact this
