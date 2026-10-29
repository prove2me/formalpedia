-- Prove2me | solution 1 for AvramDividend.Classical.bv_foldr_min_eq_finite_iInf_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:19:15.280399+00:00
-- url     : https://prove2.me/submissions/41da9eb2-23cb-4585-8038-e66e6693f516

import Mathlib
open Set
open scoped ENNReal
theorem solution
    {α : Type*} [CompleteLinearOrder α]
    (v : ℕ → α) (L : List ℕ) (H : α) :
    L.foldr (fun k u => v k ⊓ u) H =
      (⨅ (j : ℕ) (_ : j ∈ L), v j) ⊓ H := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, ih]
    simp only [List.mem_cons, iInf_or, iInf_inf_eq, iInf_iInf_eq_left, inf_assoc]
