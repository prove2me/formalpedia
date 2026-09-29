-- Prove2me | solution 1 for Freiman.cert_weighted_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:37:24.940757+00:00
-- url     : https://prove2.me/submissions/e5d927d5-f5ac-4db0-805f-95d34aa494cf

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
    ∀ v w : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, 0 ≤ v i j) → (∀ i j : Fin 3, 0 ≤ w i j) → 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, v i j*w i j := by
  intro v w hv hw
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (hv i j) (hw i j)))


#print axioms solution
