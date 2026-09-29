-- Prove2me | solution 1 for BookProof.RitzCertificate.temple_nested_certificate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T12:48:29.222216+00:00
-- url     : https://prove2.me/submissions/6cf822f8-2cae-4540-98a5-40c2c7a5b51c

import Mathlib
import Definitions.Def_ChapterRitzCertificate
import Theorems.Thm_BookProof_RitzCertificate_nested_certificate_of_bands
import Theorems.Thm_BookProof_RitzCertificate_temple_band_mem
import Theorems.Thm_BookProof_RitzCertificate_temple_width_tendsto_zero
open BookProof.RitzCertificate
open Filter Topology
open BookProof.BandEnclosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution [Nontrivial F] {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {b delta : ℝ} {x : ℕ → F} (hsep : SpectralSeparation A (sInf (spectrum ℝ A)) b)
    (hdelta : 0 < delta) (hx : ∀ m, ‖x m‖ = 1) (hle : ∀ m, rayleigh A (x m) ≤ b - delta)
    (hres : Tendsto (fun m => resid A (x m)) atTop (𝓝 0)) :
    NestedBands (runLo fun m => rayleigh A (x m) - resid A (x m) ^ 2 / (b - rayleigh A (x m)))
        (runHi fun m => rayleigh A (x m)) ∧
      (∀ m, sInf (spectrum ℝ A) ∈
        Set.Icc (runLo (fun m => rayleigh A (x m) -
            resid A (x m) ^ 2 / (b - rayleigh A (x m))) m)
          (runHi (fun m => rayleigh A (x m)) m)) ∧
      Tendsto (fun m => runHi (fun m => rayleigh A (x m)) m -
        runLo (fun m => rayleigh A (x m) -
          resid A (x m) ^ 2 / (b - rayleigh A (x m))) m) atTop (𝓝 0) := by
  let lo : ℕ → ℝ := fun m => rayleigh A (x m) - resid A (x m) ^ 2 / (b - rayleigh A (x m))
  let hi : ℕ → ℝ := fun m => rayleigh A (x m)
  have hlt (m : ℕ) : rayleigh A (x m) < b :=
    lt_of_le_of_lt (hle m) (sub_lt_self _ hdelta)
  have hmem : ∀ m, sInf (spectrum ℝ A) ∈ Set.Icc (lo m) (hi m) := fun m =>
    temple_band_mem hA hsep (hx m) (hlt m)
  have hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0) := by
    simpa [lo, hi, sub_sub_cancel] using temple_width_tendsto_zero hdelta hle hres
  simpa [lo, hi] using nested_certificate_of_bands hmem hwidth
