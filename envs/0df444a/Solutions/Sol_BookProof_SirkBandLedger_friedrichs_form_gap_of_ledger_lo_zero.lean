-- Prove2me | solution 1 for BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger_lo_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:37:56.369433+00:00
-- url     : https://prove2.me/submissions/be1202af-015a-483f-8817-bc4f20198fa0

-- Generated from ChapterSirkBandLedger.lean — solution of BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger_lo_zero
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
import Theorems.Thm_BookProof_SirkBandLedger_friedrichs_form_gap_of_ledger
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
      Set.Icc (ledgerLo L m) (ledgerHi L m)) :
    ledgerLo L 0 ≤ ritzInf H (finiteModeDomain b) ∧
      ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (S : F →L[ℂ] F),
        IsPositiveSelfAdjointExtension H A ∧ IsShiftInvert A 1 S ∧ IsSelfAdjoint S ∧
          ∀ y : Dom, ledgerLo L 0 * ‖(y : F)‖ ^ 2 ≤ quadForm A y := by

  obtain ⟨-, h2, h3⟩ :=
    friedrichs_form_gap_of_ledger b H hsym hpos hwf hritz (mu := ledgerLo L 0)
      (m₀ := 0) le_rfl
  exact ⟨h2, h3⟩
