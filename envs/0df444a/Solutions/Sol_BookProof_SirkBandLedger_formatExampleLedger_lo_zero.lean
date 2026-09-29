-- Prove2me | solution 1 for BookProof.SirkBandLedger.formatExampleLedger_lo_zero
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:11:56.045274+00:00
-- url     : https://prove2.me/submissions/ee6c2f5e-81f3-44df-b043-ddf8f27aa6f3

import Definitions.Def_ChapterSirkBandLedger
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean
open BookProof.SirkBandLedger BookProof.SirkCertificateReader BookProof.BandEnclosure
open Filter Topology
set_option autoImplicit false
set_option maxRecDepth 10000


theorem solution : ledgerLo formatExampleLedger 0 = 0.9 := by
  norm_num [ledgerLo, loQ, recAt, formatExampleLedger, Decimal.toQ]

#print axioms solution
