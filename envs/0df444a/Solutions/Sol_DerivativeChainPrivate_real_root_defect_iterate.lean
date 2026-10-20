-- Prove2me | solution 1 for DerivativeChainPrivate.real_root_defect_iterate
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:47:25.487017+00:00
-- url     : https://prove2.me/submissions/ade34b13-14ec-496e-94ad-9d816c4d818e

import Theorems.Thm_DerivativeChainPrivate_real_root_defect_derivative

set_option autoImplicit false

theorem solution (p : Polynomial ℝ) (k : ℕ) :
    ((Polynomial.derivative^[k]) p).natDegree -
        ((Polynomial.derivative^[k]) p).roots.card ≤ p.natDegree - p.roots.card := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (DerivativeChainPrivate.real_root_defect_derivative _).trans ih
