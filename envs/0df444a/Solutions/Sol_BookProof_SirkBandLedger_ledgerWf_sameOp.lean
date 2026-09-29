-- Prove2me | solution 1 for BookProof.SirkBandLedger.ledgerWf_sameOp
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:11:49.301806+00:00
-- url     : https://prove2.me/submissions/c736e3fd-1c92-4c8f-94fc-7615c94f7bfa

import Definitions.Def_ChapterSirkBandLedger
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean
open BookProof.SirkBandLedger BookProof.SirkCertificateReader BookProof.BandEnclosure
open Filter Topology
set_option autoImplicit false
set_option maxRecDepth 10000


theorem solution {L : List BandRecord} (h : LedgerWf L) {r : BandRecord}
    (hr : r ∈ L) : r.op = (L.getD 0 default).op := by
  rw [LedgerWf, ledgerWfB] at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2 r hr

#print axioms solution
