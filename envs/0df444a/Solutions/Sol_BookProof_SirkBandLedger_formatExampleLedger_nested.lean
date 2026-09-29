-- Prove2me | solution 1 for BookProof.SirkBandLedger.formatExampleLedger_nested
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T12:57:53.804866+00:00
-- url     : https://prove2.me/submissions/ee2c5828-17f2-4a14-a81a-9f315d0249ca

import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger
open BookProof.BandEnclosure
open BookProof.SirkCertificateReader

theorem solution :
    NestedBands (ledgerLo formatExampleLedger) (ledgerHi formatExampleLedger) := by
  intro m
  have hlen : formatExampleLedger.length = 3 := rfl
  by_cases hm : 2 ≤ m
  · have hstab : recAt formatExampleLedger (m + 1) = recAt formatExampleLedger m := by
      unfold recAt
      simp [hlen]
      have : min (m + 1) 2 = min m 2 := by omega
      simp [this]
    simp [ledgerLo, ledgerHi, loQ, hiQ, hstab]
  · have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · -- [1.500, 2.100] ⊆ [0.900, 2.400]
      refine Set.Icc_subset_Icc ?_ ?_
      · simp [ledgerLo, loQ, recAt, formatExampleLedger, Decimal.toQ]
        norm_num
      · simp [ledgerHi, hiQ, recAt, formatExampleLedger, Decimal.toQ]
        norm_num
    · -- [1.850, 1.960] ⊆ [1.500, 2.100]
      refine Set.Icc_subset_Icc ?_ ?_
      · simp [ledgerLo, loQ, recAt, formatExampleLedger, Decimal.toQ]
        norm_num
      · simp [ledgerHi, hiQ, recAt, formatExampleLedger, Decimal.toQ]
        norm_num
