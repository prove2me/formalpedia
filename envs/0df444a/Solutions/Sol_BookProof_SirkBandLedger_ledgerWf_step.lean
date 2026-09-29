-- Prove2me | solution 1 for BookProof.SirkBandLedger.ledgerWf_step
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:11:56.848183+00:00
-- url     : https://prove2.me/submissions/7de89132-db0d-4af2-9cd6-f0e697429177

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

theorem solution {L : List BandRecord} (h : LedgerWf L) {i : ℕ}
    (hi : i + 1 < L.length) :
    (L.getD i default).lo.toQ ≤ (L.getD (i + 1) default).lo.toQ ∧
      (L.getD (i + 1) default).hi.toQ ≤ (L.getD i default).hi.toQ := by
  rw [LedgerWf, ledgerWfB] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have hmem : i < L.length - 1 := by omega
  obtain ⟨h1, h2⟩ := h.1.2 i hmem
  exact ⟨(ritzB_Decimal_leB_iff _ _).1 h1, (ritzB_Decimal_leB_iff _ _).1 h2⟩

#print axioms solution
