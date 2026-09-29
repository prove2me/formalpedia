-- Prove2me | solution 1 for BookProof.SirkBandLedger.formatExampleLedger_parse
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:11:54.342855+00:00
-- url     : https://prove2.me/submissions/b9931f5c-36a7-49f5-8c24-7dd7b9781078

import Definitions.Def_ChapterSirkBandLedger
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean
open BookProof.SirkBandLedger BookProof.SirkCertificateReader BookProof.BandEnclosure
open Filter Topology
set_option autoImplicit false
set_option maxRecDepth 10000


theorem solution :
    parseLedger formatExampleLedgerNdjson = formatExampleLedger := by rfl

#print axioms solution
