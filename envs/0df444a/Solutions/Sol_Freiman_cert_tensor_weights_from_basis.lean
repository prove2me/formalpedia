-- Prove2me | solution 1 for Freiman.cert_tensor_weights_from_basis
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:37:05.956967+00:00
-- url     : https://prove2.me/submissions/b2b6743f-5abf-466f-bd4b-7e4eef354d27

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
    ∀ (R : CertRectangle) (r s : ℝ),
    ((∀ i : Fin 3, 0 ≤ certBernsteinBasis i ((r-R.r0)/(R.r1-R.r0))) ∧ (∑ i : Fin 3, certBernsteinBasis i ((r-R.r0)/(R.r1-R.r0))) = 1) →
    ((∀ j : Fin 3, 0 ≤ certBernsteinBasis j ((s-R.s0)/(R.s1-R.s0))) ∧ (∑ j : Fin 3, certBernsteinBasis j ((s-R.s0)/(R.s1-R.s0))) = 1) →
    (∀ i j : Fin 3, 0 ≤ certBernsteinWeight R r s i j) ∧ (∑ i : Fin 3, ∑ j : Fin 3, certBernsteinWeight R r s i j) = 1 := by
  intro R r s hr hs
  constructor
  · intro i j
    exact mul_nonneg (hr.1 i) (hs.1 j)
  · simp only [certBernsteinWeight, ← Finset.mul_sum, hs.2, mul_one, hr.2]


#print axioms solution
