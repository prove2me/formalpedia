-- Prove2me | solution 1 for Freiman.cert_field_scale
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:33:09.976168+00:00
-- url     : https://prove2.me/submissions/da9af50b-6001-4c22-80a2-8583a36d42b3

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
    ∀ (q : ℚ) (x : CertField), certFieldVal (certFieldScale q x) = (q:ℝ)*certFieldVal x := by
  intro q x
  simp only [certFieldVal, certFieldScale]
  push_cast
  ring


#print axioms solution
