-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.sum_cube_hop_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:50:37.859541+00:00
-- url     : https://prove2.me/submissions/799d4b08-c282-4966-a958-51b6940227b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.sum_cube_hop_im
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Theorems.Thm_BookProof_CarlemanTwoStep_sum_cube_splitK
import Theorems.Thm_BookProof_CarlemanTwoStep_sum_ltermG
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
    (∑ a ∈ cube d N, (rtermG u w rc k i a + ltermG u w lc k i a)).im
      = (∑ a ∈ faceK d N i k, rtermG u w rc k i a).im := by

  rw [Finset.sum_add_distrib, sum_cube_splitK d N i k (rtermG u w rc k i),
    sum_ltermG hcomp hvan N]
  simp [Complex.add_im]
