-- Prove2me | solution 1 for BookProof.SirkBandLedger.ledgerWf_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:06:23.948699+00:00
-- url     : https://prove2.me/submissions/150ac026-6fd8-409a-80d6-701244b26d81

import Definitions.Def_ChapterSirkBandLedger
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean
open BookProof.SirkBandLedger BookProof.SirkCertificateReader BookProof.BandEnclosure
open Filter Topology
set_option autoImplicit false
set_option maxRecDepth 10000


theorem solution {L : List BandRecord} (h : LedgerWf L) : L ≠ [] := by
  intro hnil
  rw [LedgerWf, ledgerWfB, hnil] at h
  simp at h

#print axioms solution
