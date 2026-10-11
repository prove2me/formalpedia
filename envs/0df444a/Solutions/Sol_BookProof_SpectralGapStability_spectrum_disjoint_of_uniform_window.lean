-- Prove2me | solution 1 for BookProof.SpectralGapStability.spectrum_disjoint_of_uniform_window
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:27.045957+00:00
-- url     : https://prove2.me/submissions/e2dbd8aa-bed9-45d3-86ae-9a268f058eea

-- Generated from ChapterSpectralGapStability.lean — solution of BookProof.SpectralGapStability.spectrum_disjoint_of_uniform_window
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
import Theorems.Thm_BookProof_SpectralGapStability_notMem_spectrum_of_uniform_gap
open BookProof.SpectralGapStability



noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F}
    (hB : IsSelfAdjoint B) {a b : ℝ}
    (hgap : ∀ lam ∈ Set.Ioo a b, ∀ m, GapAt (A m) lam (min (lam - a) (b - lam)))
    (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) :
    ∀ lam ∈ Set.Ioo a b, (lam : ℂ) ∉ spectrum ℂ B := by

  intro lam hlam
  have hd : 0 < min (lam - a) (b - lam) := lt_min (by linarith [hlam.1]) (by linarith [hlam.2])
  exact notMem_spectrum_of_uniform_gap hB hd (hgap lam hlam) hconv
