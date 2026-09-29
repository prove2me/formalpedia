-- Prove2me | solution 1 for BookProof.SirkBandLedger.ledgerWf_order
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:11:51.686433+00:00
-- url     : https://prove2.me/submissions/87acc64e-710f-44da-a9f9-abc510a48eca

import Definitions.Def_ChapterSirkBandLedger
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean
open BookProof.SirkBandLedger BookProof.SirkCertificateReader BookProof.BandEnclosure
open Filter Topology
set_option autoImplicit false
set_option maxRecDepth 10000


theorem solution {L : List BandRecord} (h : LedgerWf L) {i : ℕ}
    (hi : i < L.length) : (L.getD i default).order = i := by
  rw [LedgerWf, ledgerWfB] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.1.2 i hi

#print axioms solution
