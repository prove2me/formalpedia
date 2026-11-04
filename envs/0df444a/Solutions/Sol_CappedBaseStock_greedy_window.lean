-- Prove2me | solution 1 for CappedBaseStock.greedy_window
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T01:55:41.004322+00:00
-- url     : https://prove2.me/submissions/8646e3bb-da4f-478d-acb3-c70f91b79fb9

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

open scoped BigOperators

theorem solution
    (L : ℕ) (hL : 1 ≤ L)
    (a b : ℤ → ℝ)
    (ha : ∀ t : ℤ, 0 ≤ a t)
    (hb : ∀ t : ℤ, 0 ≤ b t)
    (hrec : ∀ t : ℤ,
      a t = max (b t - ∑ i ∈ Finset.Icc 1 L, a (t - (i : ℤ))) 0)
    (start : ℤ) (n : ℕ) (hn : 0 < n) (hlen : n ≤ L + 1) :
    (∑ i ∈ Finset.range n, a (start + (i : ℤ))) ≤
      (Finset.range n).sup'
        (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn))
        (fun i => b (start + (i : ℤ))) := by
  classical
  let B := (Finset.range n).sup'
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn))
    (fun i => b (start + (i : ℤ)))
  have hbB : ∀ i < n, b (start + (i : ℤ)) ≤ B := by
    intro i hi
    exact Finset.le_sup' (fun i : ℕ => b (start + (i : ℤ))) (Finset.mem_range.mpr hi)
  have hB : 0 ≤ B := (hb (start + (0 : ℤ))).trans (hbB 0 hn)
  have hbound : ∀ m : ℕ, m ≤ n → (∑ i ∈ Finset.range m, a (start + (i : ℤ))) ≤ B := by
    intro m
    induction m with
    | zero =>
        intro _
        simpa using hB
    | succ m ih =>
        intro hm
        rw [Finset.sum_range_succ]
        by_cases hzero : a (start + (m : ℤ)) = 0
        · simpa [hzero] using ih (by omega)
        · have hml : m ≤ L := by omega
          have hprior :
              (∑ i ∈ Finset.range m, a (start + (i : ℤ))) ≤
                ∑ i ∈ Finset.Icc 1 L, a (start + (m : ℤ) - (i : ℤ)) := by
            calc
              (∑ i ∈ Finset.range m, a (start + (i : ℤ))) =
                  ∑ i ∈ Finset.Icc 1 m, a (start + (m : ℤ) - (i : ℤ)) := by
                apply Finset.sum_bij (fun i _ => m - i)
                · intro i hi
                  simp only [Finset.mem_range] at hi
                  simp only [Finset.mem_Icc]
                  omega
                · intro i hi j hj hij
                  simp only [Finset.mem_range] at hi hj
                  omega
                · intro j hj
                  simp only [Finset.mem_Icc] at hj
                  refine ⟨m - j, Finset.mem_range.mpr (by omega), ?_⟩
                  omega
                · intro i hi
                  simp only [Finset.mem_range] at hi
                  congr 1
                  omega
              _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
                (by intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega)
                (by intro i _ _; exact ha _)
          have hrec' := hrec (start + (m : ℤ))
          have hdiff : 0 ≤ b (start + (m : ℤ)) -
              ∑ i ∈ Finset.Icc 1 L, a (start + (m : ℤ) - (i : ℤ)) := by
            by_contra hneg
            rw [max_eq_right (le_of_not_ge hneg)] at hrec'
            exact hzero hrec'
          rw [max_eq_left hdiff] at hrec'
          exact (by linarith :
            (∑ i ∈ Finset.range m, a (start + (i : ℤ))) + a (start + (m : ℤ)) ≤
              b (start + (m : ℤ))).trans (hbB m (by omega))
  exact hbound n le_rfl
