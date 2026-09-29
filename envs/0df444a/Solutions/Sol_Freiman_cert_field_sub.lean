-- Prove2me | solution 1 for Freiman.cert_field_sub
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:32:52.504979+00:00
-- url     : https://prove2.me/submissions/e370b8d2-8a7b-4771-94ce-23a62c570f8b

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
    ∀ x y : CertField, certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  intro x y
  simp only [certFieldVal, certFieldSub]
  push_cast
  ring


#print axioms solution
