-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.shifted_facesK_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:28:31.563902+00:00
-- url     : https://prove2.me/submissions/2e12ed66-254d-4b1f-a634-a5842a2b31f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.shifted_facesK_le
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Theorems.Thm_BookProof_CarlemanTwoStep_sum_range_of_multiplicity
import Theorems.Thm_BookProof_CarlemanTwoStep_shiftedK_multiplicity
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (k M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ faceK d N i k, ‖u (a + Finsupp.single i k)‖ ^ 2
      ≤ (k : ℝ) * B := by

  classical
  have hinj : ∀ N : ℕ, ∑ a ∈ faceK d N i k, ‖u (a + Finsupp.single i k)‖ ^ 2
      = ∑ b ∈ (faceK d N i k).image (fun a => a + Finsupp.single i k), ‖u b‖ ^ 2 := by
    intro N
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact add_right_cancel hxy
  simp_rw [hinj]
  exact sum_range_of_multiplicity k hbes
    (fun N => (faceK d N i k).image (fun a => a + Finsupp.single i k))
    (shiftedK_multiplicity i k) M
