-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.facesK_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:51:38.66229+00:00
-- url     : https://prove2.me/submissions/69c9c52b-7188-46b3-bd7c-3b7934dc6321
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.facesK_le
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Theorems.Thm_BookProof_CarlemanTwoStep_sum_range_of_multiplicity
import Theorems.Thm_BookProof_CarlemanTwoStep_faceK_multiplicity
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
    ∑ N ∈ Finset.range M, ∑ a ∈ faceK d N i k, ‖u a‖ ^ 2 ≤ (k : ℝ) * B := sum_range_of_multiplicity k hbes (fun N => faceK d N i k) (faceK_multiplicity i k) M
