-- Prove2me | solution 1 for BookProof.SirkBandLedger.recAt_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:11:50.179768+00:00
-- url     : https://prove2.me/submissions/3bc7dabd-20eb-42c7-85a5-72100c1cd2e0

import Definitions.Def_ChapterSirkBandLedger
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean
open BookProof.SirkBandLedger BookProof.SirkCertificateReader BookProof.BandEnclosure
open Filter Topology
set_option autoImplicit false
set_option maxRecDepth 10000


theorem solution {L : List BandRecord} {m : ℕ} (hm : L.length - 1 ≤ m) :
    recAt L m = recAt L (L.length - 1) := by
  simp [recAt, min_eq_right hm]

#print axioms solution
