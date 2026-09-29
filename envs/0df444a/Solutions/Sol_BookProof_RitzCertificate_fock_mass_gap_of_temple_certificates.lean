-- Prove2me | solution 1 for BookProof.RitzCertificate.fock_mass_gap_of_temple_certificates
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:50:01.016259+00:00
-- url     : https://prove2.me/submissions/7778ee2c-4a38-472d-bb62-5c226d542d66

-- Generated from ChapterRitzCertificate.lean — solution of BookProof.RitzCertificate.fock_mass_gap_of_temple_certificates
import Mathlib
import Definitions.Def_ChapterRitzCertificate
import Theorems.Thm_BookProof_RitzCertificate_le_runLo
import Theorems.Thm_BookProof_RitzCertificate_temple_nested_certificate
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterBandEnclosure
import Theorems.Thm_BookProof_FockOneParticleGap_fock_mass_gap_of_certified_bands_operator
open BookProof.RitzCertificate














noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]














variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]





















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial F] {A : F →L[ℂ] F}
    (hA : IsSelfAdjoint A) {bas : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ}
    (heig : ∀ k, A (bas k) = ((e k : ℝ) : ℂ) • bas k)
    {b delta mu : ℝ} {x : ℕ → F} (hsep : SpectralSeparation A (sInf (spectrum ℝ A)) b)
    (hdelta : 0 < delta) (hmu : 0 ≤ mu) (hx : ∀ m, ‖x m‖ = 1)
    (hle : ∀ m, rayleigh A (x m) ≤ b - delta)
    (hres : Tendsto (fun m => resid A (x m)) atTop (𝓝 0))
    {m₀ : ℕ} (hlo : mu ≤ rayleigh A (x m₀) -
      resid A (x m₀) ^ 2 / (b - rayleigh A (x m₀))) :
    Tendsto (runLo fun m => rayleigh A (x m) -
        resid A (x m) ^ 2 / (b - rayleigh A (x m))) atTop (𝓝 (sInf (spectrum ℝ A))) ∧
      mu ≤ sInf (spectrum ℝ A) ∧ dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by

  obtain ⟨-, hmem, hwidth⟩ := temple_nested_certificate hA hsep hdelta hx hle hres
  exact fock_mass_gap_of_certified_bands_operator hA heig hmu hmem hwidth
    (m₀ := m₀) (le_trans hlo (le_runLo (fun m => rayleigh A (x m) -
      resid A (x m) ^ 2 / (b - rayleigh A (x m))) m₀))
