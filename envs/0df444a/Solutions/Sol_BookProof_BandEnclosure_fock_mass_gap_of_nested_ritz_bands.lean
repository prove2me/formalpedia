-- Prove2me | solution 1 for BookProof.BandEnclosure.fock_mass_gap_of_nested_ritz_bands
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T09:56:35.337905+00:00
-- url     : https://prove2.me/submissions/4ef10db5-c29e-4713-8754-8bae60538c32

-- Generated from ChapterBandEnclosure.lean — solution of BookProof.BandEnclosure.fock_mass_gap_of_nested_ritz_bands
import Mathlib
import Definitions.Def_ChapterBandEnclosure
import Theorems.Thm_BookProof_BandEnclosure_ritz_band_enclosure_of_nested
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Theorems.Thm_BookProof_FockOneParticleGap_fock_mass_gap_of_certified_bands_operator
open BookProof.BandEnclosure











noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8















open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial F] (A : F →L[ℂ] F)
    (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re)
    (b : HilbertBasis ℕ ℂ F) {e : ℕ → ℝ}
    (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k)
    {lo hi : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (hnest : NestedBands lo hi)
    (hritz : ∀ m, ritzInf (finiteModeRestrict A b) (galerkinSpan b (m + 1)) ∈
      Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) :
    IsPositiveSelfAdjointExtension (finiteModeRestrict A b) (topRestrict A) ∧
      Tendsto lo atTop (𝓝 (sInf (spectrum ℝ A))) ∧ mu ≤ sInf (spectrum ℝ A) ∧
      dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by

  obtain ⟨hsel, hband⟩ := ritz_band_enclosure_of_nested A hsa hpos b hnest hritz
  exact ⟨hsel, fock_mass_gap_of_certified_bands_operator hsa heig hmu hband hwidth hlo⟩
