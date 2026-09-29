-- Prove2me | solution 1 for BookProof.FockOneParticleGap.fock_mass_gap_of_certified_bands_operator
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:37:57.878613+00:00
-- url     : https://prove2.me/submissions/231a9851-dffb-43f4-8dc3-f2a4e636a6b3

-- Generated from ChapterFockOneParticleGap.lean — solution of BookProof.FockOneParticleGap.fock_mass_gap_of_certified_bands_operator
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
import Theorems.Thm_BookProof_FockOneParticleGap_band_endpoints_tendsto
import Theorems.Thm_BookProof_FockOneParticleGap_le_of_band
import Theorems.Thm_BookProof_FockOneParticleGap_fock_gap_of_operator_spectral_edge
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_spectrum_real_bddBelow
open BookProof.FockOneParticleGap













noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology
















































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open BookProof.SirkCertifiedGap






open BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {b : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ}
    (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {lo hi : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu)
    (hband : ∀ m, sInf (spectrum ℝ A) ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) :
    Tendsto lo atTop (𝓝 (sInf (spectrum ℝ A))) ∧ mu ≤ sInf (spectrum ℝ A) ∧
      dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by

  have hedge : mu ≤ sInf (spectrum ℝ A) := le_of_band hband hlo
  have hspec : ∀ lam ∈ spectrum ℝ A, mu ≤ lam := fun lam hlam =>
    le_trans hedge (csInf_le (spectrum_real_bddBelow A hA) hlam)
  obtain ⟨hvac, hgap⟩ := fock_gap_of_operator_spectral_edge hA heig hmu hspec
  exact ⟨(band_endpoints_tendsto hband hwidth).1, hedge, hvac, hgap⟩
