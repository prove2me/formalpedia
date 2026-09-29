-- Prove2me | solution 1 for Freiman.cert_coefficient_lower_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:35:43.6498+00:00
-- url     : https://prove2.me/submissions/ae2ea89a-7e2a-49c5-bd87-bffaed4b4c29

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
    ∀ (z : CertField) (q : ℚ), certCoefficientBoundValid z q → 0 ≤ certFieldLower z := by
  intro z q h
  rcases h with ⟨hq, hb⟩
  by_cases hz : q = 0
  · simpa only [hz, if_true] using hb
  · have hlt : q < certFieldLower z := by simpa only [if_neg hz] using hb
    exact le_trans hq hlt.le


#print axioms solution
