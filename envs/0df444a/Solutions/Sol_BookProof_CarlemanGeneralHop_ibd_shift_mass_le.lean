-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.ibd_shift_mass_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:28:23.035612+00:00
-- url     : https://prove2.me/submissions/34acfa71-2806-49b0-b8e8-0beced14c99d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.ibd_shift_mass_le
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_hshift
import Theorems.Thm_BookProof_CarlemanGeneralHop_mem_ibd
import Theorems.Thm_BookProof_CarlemanGeneralHop_ibd_image_multiplicity
import Theorems.Thm_BookProof_CarlemanTwoStep_sum_range_of_multiplicity
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanGeneralHop




open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (p m : Fin d →₀ ℕ) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ b ∈ ibd d N m, ‖u (hshift p m b)‖ ^ 2 ≤ B := by

  classical
  have hinj : ∀ N : ℕ, ∑ b ∈ ibd d N m, ‖u (hshift p m b)‖ ^ 2
      = ∑ y ∈ (ibd d N m).image (hshift p m), ‖u y‖ ^ 2 := by
    intro N
    rw [Finset.sum_image]
    intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_ibd] at hx hy
    have := congrArg (hshift m p) hxy
    rwa [hshift_hshift hx.2.1, hshift_hshift hy.2.1] at this
  simp_rw [hinj]
  have := BookProof.CarlemanTwoStep.sum_range_of_multiplicity (u := u) 1 hbes
    (fun N => (ibd d N m).image (hshift p m)) (ibd_image_multiplicity p m) M
  simpa using this
