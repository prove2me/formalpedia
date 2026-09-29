-- Prove2me | solution 1 for Freiman.cert_field_add
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:32:34.717277+00:00
-- url     : https://prove2.me/submissions/f25c4a2a-d2e4-4f94-bea6-7da808c51bcd

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
    ∀ x y : CertField, certFieldVal (certFieldAdd x y) = certFieldVal x + certFieldVal y := by
  intro x y
  simp only [certFieldVal, certFieldAdd]
  push_cast
  ring


#print axioms solution
