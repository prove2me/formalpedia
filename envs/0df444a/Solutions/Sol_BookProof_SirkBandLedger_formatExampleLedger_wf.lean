-- Prove2me | solution 1 for BookProof.SirkBandLedger.formatExampleLedger_wf
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:06:21.088051+00:00
-- url     : https://prove2.me/submissions/47a431e7-6ea3-4e0b-a524-ac8efaed30b6

import Definitions.Def_ChapterSirkBandLedger
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean
open BookProof.SirkBandLedger BookProof.SirkCertificateReader BookProof.BandEnclosure
open Filter Topology
set_option autoImplicit false
set_option maxRecDepth 10000


theorem solution : LedgerWf formatExampleLedger := by decide

#print axioms solution
