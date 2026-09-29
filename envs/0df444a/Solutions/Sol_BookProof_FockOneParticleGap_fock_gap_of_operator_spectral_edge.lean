-- Prove2me | solution 1 for BookProof.FockOneParticleGap.fock_gap_of_operator_spectral_edge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:36:50.191402+00:00
-- url     : https://prove2.me/submissions/5a083ac4-0905-421c-8c75-f64d5df45417

-- Generated from ChapterFockOneParticleGap.lean — solution of BookProof.FockOneParticleGap.fock_gap_of_operator_spectral_edge
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
import Theorems.Thm_BookProof_FockOneParticleGap_dGamma_diagCol_vac
import Theorems.Thm_BookProof_FockOneParticleGap_fock_gap_quadForm
import Theorems.Thm_BookProof_FockOneParticleGap_le_eigenvalue_of_le_spectrum
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
    (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {mu : ℝ} (hmu : 0 ≤ mu)
    (hspec : ∀ lam ∈ spectrum ℝ A, mu ≤ lam) :
    dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re :=
  ⟨dGamma_diagCol_vac e,
      fun _ h0 => fock_gap_quadForm hmu (le_eigenvalue_of_le_spectrum hA heig hspec) h0⟩
