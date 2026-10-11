-- Prove2me | solution 1 for BookProof.SpectralGapStability.notMem_spectrum_of_uniform_gap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:25.808855+00:00
-- url     : https://prove2.me/submissions/a76b38b5-cf07-431a-954f-eefb2c4d2158

-- Generated from ChapterSpectralGapStability.lean — solution of BookProof.SpectralGapStability.notMem_spectrum_of_uniform_gap
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
import Theorems.Thm_BookProof_SpectralGapStability_gapAt_of_tendsto
import Theorems.Thm_BookProof_SpectralGapStability_notMem_spectrum_of_gapAt
open BookProof.SpectralGapStability



noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F}
    (hB : IsSelfAdjoint B) {lam d : ℝ} (hd : 0 < d) (hgap : ∀ m, GapAt (A m) lam d)
    (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) : (lam : ℂ) ∉ spectrum ℂ B := notMem_spectrum_of_gapAt hB hd (gapAt_of_tendsto hgap hconv)
