-- Prove2me | solution 1 for BookProof.SirkBandLedger.recAt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:11:50.911703+00:00
-- url     : https://prove2.me/submissions/34de37cd-6eba-4826-8edb-1f1c2b79dbc9

import Definitions.Def_ChapterSirkBandLedger
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean
open BookProof.SirkBandLedger BookProof.SirkCertificateReader BookProof.BandEnclosure
open Filter Topology
set_option autoImplicit false
set_option maxRecDepth 10000


theorem solution {L : List BandRecord} {m : ℕ} (hm : m < L.length) :
    recAt L m = L.getD m default := by
  have h : min m (L.length - 1) = m := min_eq_left (by omega)
  simp [recAt, h]

#print axioms solution
