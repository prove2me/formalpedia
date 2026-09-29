-- Prove2me | solution 1 for Freiman.cert_diagonal_factorization
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:59:14.961856+00:00
-- url     : https://prove2.me/submissions/773a8440-63af-4857-9a73-b04d229e8811

import Definitions.Def_Freiman_certDiagonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin

open Freiman
open scoped BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 12000000

open Freiman

theorem solution :
    ∀ (a b c : CertField) (r s : ℝ), certPolyEval (certDiagonalPolynomial a b c) r s = (r-s)*certDiagonalFactor a b c r s := by
  intro a b c r s
  simp [certPolyEval, certDiagonalPolynomial, certDiagonalFactor, certDiagonalZero,
    certFieldScale, certFieldVal, Fin.sum_univ_succ]
  ring
#print axioms solution
