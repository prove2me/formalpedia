-- Prove2me | solution 1 for BookProof.RitzCertificate.temple_band_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T12:39:57.788636+00:00
-- url     : https://prove2.me/submissions/cd5ca3af-5764-4de0-9ea6-689ff809afc5

import Mathlib
import Definitions.Def_ChapterRitzCertificate
import Theorems.Thm_BookProof_RitzCertificate_temple_lower_bound
import Theorems.Thm_BookProof_RitzCertificate_sInf_spectrum_le_rayleigh
open BookProof.RitzCertificate
open Filter Topology
open BookProof.BandEnclosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution [Nontrivial F] {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {b : ℝ} {x : F}
    (hsep : SpectralSeparation A (sInf (spectrum ℝ A)) b) (hx : ‖x‖ = 1)
    (hlt : rayleigh A x < b) :
    sInf (spectrum ℝ A) ∈
      Set.Icc (rayleigh A x - resid A x ^ 2 / (b - rayleigh A x)) (rayleigh A x) :=
  ⟨temple_lower_bound hA hsep hx hlt, sInf_spectrum_le_rayleigh A hA hx⟩
