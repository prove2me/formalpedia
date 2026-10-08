-- Prove2me | solution 1 for DemandSubstitution.Correlation.h_valuation
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:51:55.201987+00:00
-- url     : https://prove2.me/submissions/4b53224c-2990-49b8-8dac-f0d8129081eb

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_DemandSubstitution_Correlation_Setting

open DemandSubstitution.Correlation Supermodularity.Monotonicity

private theorem ds_valuation {n : ℕ} (M : Model n) (Q x y : Fin n → ℝ) (i : Fin n) :
    Ds M Q x i + Ds M Q y i = Ds M Q (x ⊔ y) i + Ds M Q (x ⊓ y) i := by
  classical
  have hc (j : Fin n) :
      M.a j i * max (x j - Q j) 0 + M.a j i * max (y j - Q j) 0 =
        M.a j i * max ((x ⊔ y) j - Q j) 0 +
          M.a j i * max ((x ⊓ y) j - Q j) 0 := by
    change _ = M.a j i * max (max (x j) (y j) - Q j) 0 +
      M.a j i * max (min (x j) (y j) - Q j) 0
    rcases le_total (x j) (y j) with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]
  have hi : x i + y i = (x ⊔ y) i + (x ⊓ y) i := by
    exact (max_add_min (x i) (y i)).symm
  unfold Ds
  have hs := Finset.sum_congr (s₁ := Finset.univ.erase i) rfl (fun j _ => hc j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
  linarith

theorem solution {n : ℕ} (M : Model n) (Q : Fin n → ℝ) (hQ : ∀ k, 0 ≤ Q k) (i : Fin n) :
    SupermodularOn (fun x => Ds M Q x i) Set.univ ∧
      SupermodularOn (fun x => -Ds M Q x i) Set.univ := by
  constructor
  · intro x hx y hy
    exact le_of_eq (ds_valuation M Q x y i)
  · intro x hx y hy
    have h := ds_valuation M Q x y i
    linarith

#print axioms solution
