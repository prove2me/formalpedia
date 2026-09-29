-- Prove2me | solution 1 for BookProof.SirkBandLedger.ledger_width_eventually_const
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:06:21.924655+00:00
-- url     : https://prove2.me/submissions/f6eeb3b5-8170-45b5-8518-2a50af751168

import Definitions.Def_ChapterSirkBandLedger
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean
open BookProof.SirkBandLedger BookProof.SirkCertificateReader BookProof.BandEnclosure
open Filter Topology
set_option autoImplicit false
set_option maxRecDepth 10000
private theorem ritzB_recAt_of_ge {L : List BandRecord} {m : ℕ} (hm : L.length - 1 ≤ m) :
    recAt L m = recAt L (L.length - 1) := by
  simp [recAt, min_eq_right hm]

theorem solution (L : List BandRecord) {m : ℕ}
    (hm : L.length - 1 ≤ m) :
    ledgerHi L m - ledgerLo L m
      = ledgerHi L (L.length - 1) - ledgerLo L (L.length - 1) := by
  simp [ledgerHi, ledgerLo, hiQ, loQ, ritzB_recAt_of_ge hm]

#print axioms solution
