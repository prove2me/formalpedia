-- Prove2me | solution 1 for Freiman.cert_radical_square_certificates
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:34:07.0494+00:00
-- url     : https://prove2.me/submissions/7eaf0d71-4b7e-40c4-b9e7-e4aad2d7d7f5

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
    (0 ≤ (certSqrt3Lower:ℝ) ∧ 0 ≤ (certSqrt3Upper:ℝ) ∧ (certSqrt3Lower:ℝ)^2 < 3 ∧ (3:ℝ) < (certSqrt3Upper:ℝ)^2) ∧
    (0 ≤ (certSqrt7Lower:ℝ) ∧ 0 ≤ (certSqrt7Upper:ℝ) ∧ (certSqrt7Lower:ℝ)^2 < 7 ∧ (7:ℝ) < (certSqrt7Upper:ℝ)^2) ∧
    (0 ≤ (certSqrt21Lower:ℝ) ∧ 0 ≤ (certSqrt21Upper:ℝ) ∧ (certSqrt21Lower:ℝ)^2 < 21 ∧ (21:ℝ) < (certSqrt21Upper:ℝ)^2) := by
  norm_num [certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper,
    certSqrt21Lower, certSqrt21Upper]


#print axioms solution
