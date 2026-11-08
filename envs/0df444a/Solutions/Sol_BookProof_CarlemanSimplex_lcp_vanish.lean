-- Prove2me | solution 1 for BookProof.CarlemanSimplex.lcp_vanish
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:10:59.876363+00:00
-- url     : https://prove2.me/submissions/7af22600-1b8b-4f73-88a7-355b4733ddc1

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.lcp_vanish
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

theorem solution (i j : Fin d) (a : Fin d →₀ ℕ) (h : ¬ pvec i j ≤ a) : lcp a i j = 0 := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · have hle : ¬ (2 ≤ a i) := by
      intro h2
      refine h ?_
      rw [Finsupp.le_def]
      intro k
      by_cases hk : k = i
      · subst hk
        simpa [pvec] using h2
      · simp [pvec, Ne.symm hk]
    rcases Nat.lt_or_ge (a i) 1 with h0 | h1
    · have hai : a i = 0 := by omega
      rw [lcp, hai]
      simp
    · have hz : ((a - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) = 0 := by
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      rw [lcp, hz]
      simp
  · have hor : a i = 0 ∨ a j = 0 := by
      by_contra hc
      push_neg at hc
      refine h ?_
      rw [Finsupp.le_def]
      intro k
      by_cases hki : k = i
      · subst hki
        have hp : (pvec k j : Fin d →₀ ℕ) k = 1 := by
          simp [pvec, hij]
        rw [hp]
        omega
      · by_cases hkj : k = j
        · subst hkj
          have hp : (pvec i k : Fin d →₀ ℕ) k = 1 := by
            simp [pvec, Ne.symm hki]
          rw [hp]
          omega
        · simp [pvec, Ne.symm hki, Ne.symm hkj]
    rcases hor with h0 | h0
    · rw [lcp, h0]
      simp
    · have hz : ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) = 0 := by
        simp only [Finsupp.tsub_apply, Finsupp.single_apply, h0]
        omega
      rw [lcp, hz]
      simp
