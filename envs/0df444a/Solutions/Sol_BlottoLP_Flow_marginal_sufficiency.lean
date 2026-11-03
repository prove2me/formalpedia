-- Prove2me | solution 1 for BlottoLP.Flow.marginal_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:12:35.415268+00:00
-- url     : https://prove2.me/submissions/39046718-2da7-4481-a873-f59c5876e7be

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model

open BlottoLP.Flow Finset in
theorem solution (I : Instance) (σ : Pure I.K I.A → ℝ) (τ : Pure I.K I.B → ℝ) :
    expPayoff I σ τ =
      ∑ k, ∑ l : Fin (I.A + 1), ∑ m : Fin (I.B + 1),
        marginal σ (k, l) * marginal τ (k, m) * I.U k l m := by
  have h1 : expPayoff I σ τ = ∑ k, ∑ x, ∑ y, σ x * τ y * I.U k (x.1 k) (y.1 k) := by
    unfold expPayoff expPay payoff
    simp only [mul_sum]
    calc ∑ x, ∑ y, ∑ k, σ x * τ y * I.U k (x.1 k) (y.1 k)
        = ∑ x, ∑ k, ∑ y, σ x * τ y * I.U k (x.1 k) (y.1 k) :=
          sum_congr rfl fun x _ => sum_comm
      _ = ∑ k, ∑ x, ∑ y, σ x * τ y * I.U k (x.1 k) (y.1 k) := sum_comm
  rw [h1]
  refine sum_congr rfl fun k _ => ?_
  symm
  calc ∑ l : Fin (I.A + 1), ∑ m : Fin (I.B + 1),
        marginal σ (k, l) * marginal τ (k, m) * I.U k l m
      = ∑ l : Fin (I.A + 1), ∑ x ∈ univ.filter (fun x : Pure I.K I.A => x.1 k = l),
          ∑ m : Fin (I.B + 1), ∑ y ∈ univ.filter (fun y : Pure I.K I.B => y.1 k = m),
            σ x * τ y * I.U k (x.1 k) (y.1 k) := by
        refine sum_congr rfl fun l _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun m _ => ?_
        unfold marginal
        rw [sum_mul_sum, sum_mul]
        refine sum_congr rfl fun x hx => ?_
        rw [sum_mul]
        refine sum_congr rfl fun y hy => ?_
        simp only [mem_filter, mem_univ, true_and] at hx hy
        rw [hx, hy]
    _ = ∑ x, ∑ y, σ x * τ y * I.U k (x.1 k) (y.1 k) := by
        rw [sum_fiberwise (s := univ) (g := fun x : Pure I.K I.A => x.1 k)
          (f := fun x => ∑ m : Fin (I.B + 1), ∑ y ∈ univ.filter (fun y : Pure I.K I.B => y.1 k = m),
            σ x * τ y * I.U k (x.1 k) (y.1 k))]
        refine sum_congr rfl fun x _ => ?_
        exact sum_fiberwise (s := univ) (g := fun y : Pure I.K I.B => y.1 k)
          (f := fun y => σ x * τ y * I.U k (x.1 k) (y.1 k))
