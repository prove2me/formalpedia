-- Prove2me | solution 1 for Freiman.cert_bound_pair_incompatible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:35:25.925982+00:00
-- url     : https://prove2.me/submissions/701bc500-271e-4b13-9beb-b25ea0fd7362

import Definitions.Def_Freiman_certificates
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

open Freiman
open scoped BigOperators


theorem solution :
    ∀ (l u : CertBound) (r s q : ℝ), l.lower=true → u.lower=false →
    (certThresholdVal u.threshold r s < certThresholdVal l.threshold r s ∨
      (certThresholdVal u.threshold r s ≤ certThresholdVal l.threshold r s ∧ (l.strict=true ∨ u.strict=true))) →
    ¬ (certBoundHolds l r s q ∧ certBoundHolds u r s q) := by
  intro l u r s q hl hu h
  simp only [certBoundHolds, hl, hu, Bool.false_eq_true, if_true, if_false]
  cases hs1 : l.strict <;> cases hs2 : u.strict <;>
    simp_all only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false,
      true_or, false_or, or_false, and_false, or_true, and_true]
  all_goals intro hh; rcases hh with ⟨h1,h2⟩
  all_goals first | linarith | (rcases h with h|h <;> linarith)


#print axioms solution
