-- Prove2me | solution 1 for Freiman.cert_basis_partition
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:36:43.267641+00:00
-- url     : https://prove2.me/submissions/fede4faf-0bb5-417a-9a33-b0568f84f00a

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
    ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → (∀ i : Fin 3, 0 ≤ certBernsteinBasis i t) ∧ (∑ i : Fin 3, certBernsteinBasis i t) = 1 := by
  intro t ht
  constructor
  · intro i
    fin_cases i <;> norm_num [certBernsteinBasis] <;>
      nlinarith [ht.1, ht.2, sq_nonneg t, sq_nonneg (1-t)]
  · simp [Fin.sum_univ_succ, certBernsteinBasis]
    ring


#print axioms solution
