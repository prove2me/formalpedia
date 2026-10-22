-- Prove2me | solution 1 for BudgetCournot.Equilibrium.identity_after_B12
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:10:59.601983+00:00
-- url     : https://prove2.me/submissions/5ca087d4-fd8b-47e1-8fa5-2b7eac036e30

import Mathlib
set_option autoImplicit false
open Finset

theorem solution {N : ℕ} (lam α : Fin N → ℝ)
    (h : ∀ i, α i = ((i : ℕ) + 1 : ℝ) * lam i - ∑ k ∈ univ.filter (fun k => k < i), lam k)
    (n : ℕ) (hn : n ≤ N) :
    (∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < n), lam k) / (1 + (n : ℝ)) =
      ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < n),
        α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ)) := by
  have gen : ∀ (g : Fin N → ℝ) (m : ℕ), m ≤ N →
      ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < m), g k =
        ∑ i ∈ range m, (if hi : i < N then g ⟨i, hi⟩ else 0) := by
    intro g m hm
    set G : ℕ → ℝ := fun i => if hi : i < N then g ⟨i, hi⟩ else 0 with hG
    calc ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < m), g k
        = ∑ k : Fin N, if (k : ℕ) < m then g k else 0 := Finset.sum_filter _ _
      _ = ∑ k : Fin N, (fun i : ℕ => if i < m then G i else 0) k.val := by
          apply Finset.sum_congr rfl
          intro k _
          simp [hG, k.2]
      _ = ∑ i ∈ range N, (if i < m then G i else 0) :=
          Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < m then G i else 0) N
      _ = ∑ i ∈ range m, G i := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext i
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
  set L : ℕ → ℝ := fun i => if hi : i < N then lam ⟨i, hi⟩ else 0 with hL
  set a : ℕ → ℝ := fun k => ((k : ℝ) + 1) * L k - ∑ i ∈ range k, L i with ha
  have hα : ∀ k : Fin N, α k = a k := by
    intro k
    have hf : univ.filter (fun j : Fin N => j < k) = univ.filter (fun j : Fin N => (j : ℕ) < (k : ℕ)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Iff.rfl
    rw [h k, hf, gen lam k (by omega)]
    have hLk : L (k : ℕ) = lam k := by
      show (if hi : (k : ℕ) < N then lam ⟨k, hi⟩ else 0) = lam k
      rw [dif_pos k.2]
    show _ = (((k : ℕ) : ℝ) + 1) * L k - ∑ i ∈ range k, L i
    rw [hLk] <;> rfl
  have main : ∀ m : ℕ, (∑ i ∈ range m, L i) / (1 + (m : ℝ)) =
      ∑ k ∈ range m, a k / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
      have h1 : (1 + (m : ℝ)) ≠ 0 := by positivity
      have h2 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have h3 : ((m : ℝ) + 2) ≠ 0 := by positivity
      have h4 : (1 + ((m + 1 : ℕ) : ℝ)) ≠ 0 := by push_cast; positivity
      simp only [ha]
      push_cast
      field_simp
      ring
  rw [gen lam n hn]
  have : ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < n),
        α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ)) =
      ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < n),
        (fun k : Fin N => a k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ))) k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hα k]
  rw [this, gen (fun k : Fin N => a k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ))) n hn]
  rw [main n]
  apply Finset.sum_congr rfl
  intro i hi
  have : i < N := by have := Finset.mem_range.mp hi; omega
  simp [this]
