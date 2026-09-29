-- Prove2me | solution 1 for Freiman.middle_cert_proof_from_pair_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T23:00:27.129984+00:00
-- url     : https://prove2.me/submissions/1be700f5-80c2-4c2b-8c50-730ab07df107

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

set_option maxHeartbeats 0

theorem solution :
    (∀ (C : MiddleCertCatalog) (p : MiddleCertPair), middleCertWitnessesValid C → middleCertPairValid C p 0 → ∀ r s q : ℝ, certRectangleMem middleCertRectangle r s → ¬ (certBoundHolds (middleCertBound C p.lowerBound) r s q ∧ certBoundHolds (middleCertBound C p.upperBound) r s q)) → (∀ (w : CertDiagonalData), certDiagonalDataValid w → ∀ r s : ℝ, certRectangleMem w.rectangle r s → certDiagonalSide w r s → certThresholdVal w.upperThreshold r s ≤ certThresholdVal w.lowerThreshold r s) → ∀ (C : MiddleCertCatalog) (p : MiddleCertProof), middleCertWitnessesValid C → middleCertProofValid C p → middleCertProofSound C p := by
  intro hpair hdiag C proof hw hp
  intro r s q hr hb
  have diagonal_excludes (pair : MiddleCertPair) (direction : ℤ)
      (hne : direction ≠ 0) (hvalid : middleCertPairValid C pair direction)
      (hside : if direction = 1 then s ≤ r else r ≤ s)
      (hholds : certBoundHolds (middleCertBound C pair.lowerBound) r s q ∧
        certBoundHolds (middleCertBound C pair.upperBound) r s q) : False := by
    rcases hvalid with ⟨hpos, hlen, hlo, hup, hfirst, hsecond, hdir, hstrict⟩
    have hi : pair.witness - 1 < C.witnesses.length := by omega
    have hmem : middleCertWitness C pair.witness ∈ C.witnesses := by
      simp only [middleCertWitness, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    have hv := hw _ hmem
    rcases hv with ⟨_, _, _, _, _, _, hv⟩
    rw [hdir] at hv
    simp only [hne, ite_false] at hv hstrict
    have hds : certDiagonalSide (middleCertDiagonalWitness C (middleCertWitness C pair.witness)) r s := by
      simpa only [certDiagonalSide, middleCertDiagonalWitness, hdir, decide_eq_true_eq] using hside
    have hord := hdiag _ hv.2.2 r s hr hds
    change certThresholdVal (middleCertThreshold C (middleCertWitness C pair.witness).second) r s ≤
      certThresholdVal (middleCertThreshold C (middleCertWitness C pair.witness).first) r s at hord
    rw [← hfirst, ← hsecond] at hord
    rcases hholds with ⟨hl, hu⟩
    simp only [certBoundHolds, middleCertBound, hlo, hup, Bool.false_eq_true,
      ite_true, ite_false] at hl hu
    rcases hstrict with hs | hs
    · rw [hs] at hl
      simp only [ite_true] at hl
      cases ht : pair.upperBound.strict <;> simp only [ht, Bool.false_eq_true,
        ite_false, ite_true] at hu <;> linarith
    · rw [hs] at hu
      simp only [ite_true] at hu
      cases ht : pair.lowerBound.strict <;> simp only [ht, Bool.false_eq_true,
        ite_false, ite_true] at hl <;> linarith
  cases proof with
  | pair p =>
      exact hpair C p hw hp r s q hr (hb p (by simp [middleCertProofPairs]))
  | diagonal a b =>
      rcases hp with ⟨ha, hbvalid⟩
      rcases le_total s r with hsr | hrs
      · exact diagonal_excludes a 1 (by decide) ha (by simpa using hsr)
          (hb a (by simp [middleCertProofPairs]))
      · exact diagonal_excludes b (-1) (by decide) hbvalid (by simpa using hrs)
          (hb b (by simp [middleCertProofPairs]))

#print axioms solution
