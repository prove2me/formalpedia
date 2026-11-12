-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.sum_ltermG
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-11T07:38:18.363923+00:00
-- url     : https://prove2.me/submissions/826c722e-3fd4-40cc-84a5-09e79b42df3c

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.sum_ltermG
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Theorems.Thm_BookProof_CarlemanTwoStep_sum_shiftK
import Theorems.Thm_BookProof_CarlemanTwoStep_ltermG_shift
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {w : ℂ} {rc lc : (Fin d →₀ ℕ) → Fin d → ℝ} {k : ℕ} {i : Fin d}
    (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + Finsupp.single i k) i = rc a i)
    (hvan : ∀ a : Fin d →₀ ℕ, a i < k → lc a i = 0) (N : ℕ) :
    ∑ a ∈ cube d N, ltermG u w lc k i a
      = (starRingEnd ℂ) (∑ a ∈ innK d N i k, rtermG u w rc k i a) := by

  rw [sum_shiftK d N i k (ltermG u w lc k i) (fun a ha => by rw [ltermG, hvan a ha]; simp),
    map_sum]
  exact Finset.sum_congr rfl fun b _ => ltermG_shift hcomp b
