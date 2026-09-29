-- Prove2me | solution 1 for BookProof.SirkBandLedger.ledgerLo_le_ledgerHi
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:06:24.791667+00:00
-- url     : https://prove2.me/submissions/29db5f13-ef45-49eb-9c2a-bd786033df10

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

private theorem ritzB_ledgerWf_ne_nil {L : List BandRecord} (h : LedgerWf L) : L ≠ [] := by
  intro hnil
  rw [LedgerWf, ledgerWfB, hnil] at h
  simp at h

private theorem ritzB_ledgerWf_enclosing {L : List BandRecord} (h : LedgerWf L) {r : BandRecord}
    (hr : r ∈ L) : r.lo.toQ ≤ r.hi.toQ := by
  rw [LedgerWf, ledgerWfB] at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact (ritzB_Decimal_leB_iff _ _).1 (h.2 r hr)

theorem solution {L : List BandRecord} (h : LedgerWf L) (m : ℕ) :
    ledgerLo L m ≤ ledgerHi L m := by
  have hne := ritzB_ledgerWf_ne_nil h
  have hlen : 0 < L.length := List.length_pos_iff.mpr hne
  have hlt : min m (L.length - 1) < L.length := lt_of_le_of_lt (min_le_right _ _) (by omega)
  have hmem : recAt L m ∈ L := by
    simp only [recAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact List.getElem_mem hlt
  have hle := ritzB_ledgerWf_enclosing h hmem
  simp only [ledgerLo, ledgerHi, loQ, hiQ]
  exact_mod_cast hle

#print axioms solution
