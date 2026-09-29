-- Prove2me | solution 1 for Freiman.cert_coefficient_lower_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:36:02.024265+00:00
-- url     : https://prove2.me/submissions/630da62e-a9fe-477f-821c-b956ce1ee92c

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
    ∀ (z : CertField) (q : ℚ), certCoefficientBoundValid z q → 0 < q → 0 < certFieldLower z := by
  intro z q h hq
  have hz : q ≠ 0 := ne_of_gt hq
  have hb : q < certFieldLower z := by simpa only [if_neg hz] using h.2
  exact lt_trans hq hb


#print axioms solution
