-- Prove2me | solution 1 for BookProof.SirkBandLedger.ledger_width_tendsto_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:11:55.192522+00:00
-- url     : https://prove2.me/submissions/b36205e3-29d0-4f6a-9528-74807932959a

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

private theorem ritzB_ledger_width_eventually_const (L : List BandRecord) {m : ℕ}
    (hm : L.length - 1 ≤ m) :
    ledgerHi L m - ledgerLo L m
      = ledgerHi L (L.length - 1) - ledgerLo L (L.length - 1) := by
  simp [ledgerHi, ledgerLo, hiQ, loQ, ritzB_recAt_of_ge hm]

theorem solution (L : List BandRecord) :
    Filter.Tendsto (fun m => ledgerHi L m - ledgerLo L m) Filter.atTop (nhds 0) ↔
      ledgerHi L (L.length - 1) - ledgerLo L (L.length - 1) = 0 := by
  have hev : (fun m => ledgerHi L m - ledgerLo L m) =ᶠ[Filter.atTop]
      (fun _ => ledgerHi L (L.length - 1) - ledgerLo L (L.length - 1)) := by
    filter_upwards [Filter.eventually_ge_atTop (L.length - 1)] with m hm
    exact ritzB_ledger_width_eventually_const L hm
  rw [Filter.tendsto_congr' hev]
  exact tendsto_const_nhds_iff

#print axioms solution
