-- Prove2me | solution 1 for BookProof.SirkBandLedger.ritz_band_enclosure_of_ledger
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:35:57.02066+00:00
-- url     : https://prove2.me/submissions/7249bccf-ebe0-44b3-b537-b905b8e72f2b

-- Generated from ChapterSirkBandLedger.lean — solution of BookProof.SirkBandLedger.ritz_band_enclosure_of_ledger
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
import Theorems.Thm_BookProof_SirkBandLedger_nestedBands_of_wf
import Theorems.Thm_BookProof_BandEnclosure_ritz_band_enclosure_of_nested
open BookProof.SirkBandLedger
















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure



































open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial F] (A : F →L[ℂ] F)
    (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re)
    (b : HilbertBasis ℕ ℂ F) {L : List BandRecord} (hwf : LedgerWf L)
    (hritz : ∀ m, ritzInf (finiteModeRestrict A b) (galerkinSpan b (m + 1)) ∈
      Set.Icc (ledgerLo L m) (ledgerHi L m)) :
    IsPositiveSelfAdjointExtension (finiteModeRestrict A b) (topRestrict A) ∧
      ∀ m, sInf (spectrum ℝ A) ∈ Set.Icc (ledgerLo L m) (ledgerHi L m) := ritz_band_enclosure_of_nested A hsa hpos b (nestedBands_of_wf hwf) hritz
