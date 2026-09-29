-- Prove2me | solution 1 for BookProof.SirkBandLedger.ledgerWf_enclosing
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:11:48.558428+00:00
-- url     : https://prove2.me/submissions/47308f7a-139b-44e5-a80a-61ed82c02f3a

import Definitions.Def_ChapterSirkBandLedger
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean
open BookProof.SirkBandLedger BookProof.SirkCertificateReader BookProof.BandEnclosure
open Filter Topology
set_option autoImplicit false
set_option maxRecDepth 10000
private theorem ritzB_Decimal_leB_iff (d e : Decimal) : Decimal.leB d e ↔ d.toQ ≤ e.toQ := by
  have hd : (0 : ℚ) < (10 : ℚ) ^ d.exp := by positivity
  have he : (0 : ℚ) < (10 : ℚ) ^ e.exp := by positivity
  rw [Decimal.toQ, Decimal.toQ, div_le_div_iff₀ hd he, Decimal.leB]
  constructor
  · intro h
    have : ((d.mant * 10 ^ e.exp : ℤ) : ℚ) ≤ ((e.mant * 10 ^ d.exp : ℤ) : ℚ) := by
      exact_mod_cast h
    push_cast at this
    linarith
  · intro h
    have : ((d.mant * 10 ^ e.exp : ℤ) : ℚ) ≤ ((e.mant * 10 ^ d.exp : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast this

theorem solution {L : List BandRecord} (h : LedgerWf L) {r : BandRecord}
    (hr : r ∈ L) : r.lo.toQ ≤ r.hi.toQ := by
  rw [LedgerWf, ledgerWfB] at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact (ritzB_Decimal_leB_iff _ _).1 (h.2 r hr)

#print axioms solution
