-- Prove2me | solution 1 for Freiman.cert_field_mul
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:33:30.405447+00:00
-- url     : https://prove2.me/submissions/3c344ff7-c835-4caa-9150-c53e55202d8d

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
    ∀ x y : CertField, certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y := by
  intro x y
  have h3 : Real.sqrt (3:ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h7 : Real.sqrt (7:ℝ) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h37 : Real.sqrt (21:ℝ) = Real.sqrt 3 * Real.sqrt 7 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  simp only [certFieldVal, certFieldMul]
  push_cast
  rw [h37]
  ring_nf
  simp only [h3, h7]
  ring


#print axioms solution
