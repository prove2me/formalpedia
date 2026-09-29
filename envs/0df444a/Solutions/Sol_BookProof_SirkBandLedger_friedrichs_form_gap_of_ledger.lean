-- Prove2me | solution 1 for BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:35:56.218114+00:00
-- url     : https://prove2.me/submissions/af631ea5-3d9c-488c-a9f6-67dfd1f6a7eb

-- Generated from ChapterSirkBandLedger.lean — solution of BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
import Theorems.Thm_BookProof_SirkBandLedger_nestedBands_of_wf
import Theorems.Thm_BookProof_BandEnclosure_friedrichs_form_gap_of_nested_ritz_bands
open BookProof.SirkBandLedger
















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure



































open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]




open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x)
    {L : List BandRecord} (hwf : LedgerWf L)
    (hritz : ∀ m, ritzInf H (galerkinSpan b (m + 1)) ∈
      Set.Icc (ledgerLo L m) (ledgerHi L m))
    {mu : ℝ} {m₀ : ℕ} (hlo : mu ≤ ledgerLo L m₀) :
    (∀ m, ritzInf H (finiteModeDomain b) ∈ Set.Icc (ledgerLo L m) (ledgerHi L m)) ∧
      mu ≤ ritzInf H (finiteModeDomain b) ∧
      ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (S : F →L[ℂ] F),
        IsPositiveSelfAdjointExtension H A ∧ IsShiftInvert A 1 S ∧ IsSelfAdjoint S ∧
          ∀ y : Dom, mu * ‖(y : F)‖ ^ 2 ≤ quadForm A y := friedrichs_form_gap_of_nested_ritz_bands b H hsym hpos (nestedBands_of_wf hwf) hritz hlo
