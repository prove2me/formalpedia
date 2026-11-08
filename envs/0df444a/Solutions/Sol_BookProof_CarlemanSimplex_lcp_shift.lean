-- Prove2me | solution 1 for BookProof.CarlemanSimplex.lcp_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:09:34.097735+00:00
-- url     : https://prove2.me/submissions/644b2b4d-8783-47f6-bef0-6102cda0ce4c

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.lcp_shift
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
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

theorem solution (i j : Fin d) (a : Fin d →₀ ℕ) :
    lcp (a + pvec i j) i j = rcp a i j := by
  classical
  by_cases hij : i = j
  · subst hij
    have h1 : ((a + pvec i i : Fin d →₀ ℕ) i : ℕ) = a i + 2 := by
      simp [pvec]
    have h2 : (((a + pvec i i) - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) = a i + 1 := by
      simp [pvec, Finsupp.tsub_apply]
    have h3 : (((a + Finsupp.single i 1 : Fin d →₀ ℕ)) i : ℕ) = a i + 1 := by simp
    rw [lcp, rcp, h1, h2, h3]
    push_cast
    ring_nf
  · have h1 : ((a + pvec i j : Fin d →₀ ℕ) i : ℕ) = a i + 1 := by
      simp [pvec, hij]
    have h2 : (((a + pvec i j) - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) = a j + 1 := by
      simp [pvec, Finsupp.tsub_apply, Ne.symm hij]
    have h3 : (((a + Finsupp.single j 1 : Fin d →₀ ℕ)) i : ℕ) = a i := by
      simp [Ne.symm hij]
    rw [lcp, rcp, h1, h2, h3]
    push_cast
    ring
