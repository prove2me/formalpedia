-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.obd_shift_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:28:14.782195+00:00
-- url     : https://prove2.me/submissions/7bc4f8bb-a93f-4275-8106-380729a0615d

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.obd_shift_mass_le
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_hshift
import Theorems.Thm_BookProof_CarlemanGeneralHop_mem_obd
import Theorems.Thm_BookProof_CarlemanGeneralHop_obd_image_multiplicity
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
    (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ obd d N p m, ‖u (hshift p m a)‖ ^ 2 ≤ 2 * B := by

  classical
  have hinj : ∀ N : ℕ, ∑ a ∈ obd d N p m, ‖u (hshift p m a)‖ ^ 2
      = ∑ y ∈ (obd d N p m).image (hshift p m), ‖u y‖ ^ 2 := by
    intro N
    rw [Finset.sum_image]
    intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_obd] at hx hy
    have := congrArg (hshift m p) hxy
    rwa [hshift_hshift hx.2.1, hshift_hshift hy.2.1] at this
  simp_rw [hinj]
  have := BookProof.CarlemanTwoStep.sum_range_of_multiplicity (u := u) 2 hbes
    (fun N => (obd d N p m).image (hshift p m)) (obd_image_multiplicity p m hp) M
  simpa using this
