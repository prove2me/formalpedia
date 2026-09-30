-- Prove2me | solution 1 for BurauFaithful.sl2_neg_one_zpow_even
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T11:01:45.688344+00:00
-- url     : https://prove2.me/submissions/a29865d1-b90c-4792-91e6-d45fa0bc57c7

/-
`BurauFaithful.sl2_neg_one_zpow_even`: the parity input of the assembly.

In the final assembly of NOTES_BURAU.md (SESSION 14) one gets `β = Δ^{2m}` from the injectivity of
the descent section, and then uses `φ(Δ²) = -I` (Proved on the platform as
`BurauFaithful.spec_reduced_fullTwist_sq`) to deduce that `m` is even: `1 = φ(β) = (-I)^m`.
This file records the group-theoretic input: in `SL(2,ℤ)` the element `-1` has order `2`, so
`(-1)^m = 1` forces `m` to be even.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem solution (m : ℤ) (h : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ^ m = 1) :
    ∃ k : ℤ, m = 2 * k := by
  have hne : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ≠ 1 := by
    intro hc
    have h00 := congrArg
      (fun X : Matrix.SpecialLinearGroup (Fin 2) ℤ => (X : Matrix (Fin 2) (Fin 2) ℤ) 0 0) hc
    simp at h00
  have hone : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ^ (2 : ℕ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hord : orderOf (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) = 2 :=
    orderOf_eq_prime hone hne
  have hdvd : (orderOf (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) : ℤ) ∣ m :=
    orderOf_dvd_iff_zpow_eq_one.mpr h
  rw [hord] at hdvd
  exact hdvd
