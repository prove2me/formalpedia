-- Prove2me | solution 1 for BookProof.CarlemanSimplex.shifted_sBd_mass_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:50:09.391583+00:00
-- url     : https://prove2.me/submissions/bb2d95f4-c7e7-4e2f-9754-aec4b11e1b21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.shifted_sBd_mass_le
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_shifted_sBd_multiplicity
import Theorems.Thm_BookProof_CarlemanTwoStep_sum_range_of_multiplicity
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (P : Fin d →₀ ℕ) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ sBd d N (deg P), ‖u (a + P)‖ ^ 2 ≤ ((deg P : ℕ) : ℝ) * B := by

  classical
  have hinj : ∀ N : ℕ, ∑ a ∈ sBd d N (deg P), ‖u (a + P)‖ ^ 2
      = ∑ b ∈ (sBd d N (deg P)).image (fun a => a + P), ‖u b‖ ^ 2 := by
    intro N
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact add_right_cancel hxy
  simp_rw [hinj]
  exact sum_range_of_multiplicity (deg P) hbes
    (fun N => (sBd d N (deg P)).image (fun a => a + P))
    (shifted_sBd_multiplicity P) M
