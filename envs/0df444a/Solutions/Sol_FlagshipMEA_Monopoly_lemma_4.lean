-- Prove2me | solution 1 for FlagshipMEA.Monopoly.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:57:59.477436+00:00
-- url     : https://prove2.me/submissions/dad957bc-4542-42e4-8ae2-376415b9f997

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model
import Theorems.Thm_FlagshipMEA_Monopoly_lemma_3
import Theorems.Thm_FlagshipMEA_Monopoly_eq_C9
import Theorems.Thm_FlagshipMEA_Monopoly_index_revenue

open FlagshipMEA.Monopoly

theorem solution {n : ℕ} (D : Data n) (hS : D.Standing)
    (hn : 0 < n) (M : ℝ) (hM : 0 < M) :
    ∃ k : Fin n, D.IsArgmaxR M k ∧
      (∀ m : Fin n → ℝ, Feasible m → tme m = M →
        D.revenue m ≤ D.revenue (fun j => if j = k then M else 0)) ∧
      (∀ m : Fin n → ℝ, Feasible m → tme m = M →
        (∀ m' : Fin n → ℝ, Feasible m' → tme m' = M →
          D.revenue m' ≤ D.revenue m) →
        ∀ i, 0 < m i → D.IsArgmaxR M i) := by
  have hmk := hS.2.1
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k, hk⟩ := Finite.exists_max (fun i => D.R i M)
  have hA : ∀ i, 0 ≤ D.A i M := by
    intro i
    unfold Data.A
    have h1 : 0 ≤ ∑ j, Real.exp ((D.u j + D.θ) / D.lam) * D.markup j :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (Real.exp_pos _).le (hmk j).le)
    have := mul_nonneg (Real.exp_pos (D.u i / D.lam)).le (hmk i).le
    have h2 : 0 ≤ 1 / M := by positivity
    nlinarith [mul_nonneg h2 h1]
  have hB : ∀ i, 0 < D.B i M := by
    intro i
    unfold Data.B
    have h1 : 0 ≤ ∑ j, Real.exp ((D.u j + D.θ) / D.lam) :=
      Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
    have h2 : 0 < 1 / M := by positivity
    have := Real.exp_pos (D.u i / D.lam)
    nlinarith [mul_nonneg h2.le h1]
  -- the concentrated allocation earns the index
  have hconc : D.revenue (fun j => if j = k then M else 0) = D.R k M :=
    (index_revenue D hS k M hM).symm
  -- for any allocation with TME `M`, the revenue is the weighted ratio (C-9)
  have key : ∀ m : Fin n → ℝ, Feasible m → tme m = M →
      ∃ k' : Fin n, (∀ i, D.R i M ≤ D.R k' M) ∧ D.revenue m ≤ D.R k' M ∧
        (D.revenue m = D.R k' M ↔ ∀ i, m i ≠ 0 → D.R i M = D.R k' M) := by
    intro m hm htme
    have hpos : 0 < tme m := htme ▸ hM
    have hrev := eq_C9 D hS m hm hpos
    rw [htme] at hrev
    have hsum : 0 < ∑ i, m i := hpos
    obtain ⟨k', h1, h2, h3⟩ := lemma_3 hn (fun i => D.A i M) (fun i => D.B i M) m hA hB hm hsum
    refine ⟨k', h1, ?_, ?_⟩
    · rw [hrev]; exact h2
    · rw [hrev]; exact h3
  have hRk : ∀ k' : Fin n, (∀ i, D.R i M ≤ D.R k' M) → D.R k' M = D.R k M :=
    fun k' hk' => le_antisymm (hk k') (hk' k)
  have hfeas : Feasible (fun j : Fin n => if j = k then M else 0) := by
    intro j; dsimp only; split_ifs <;> linarith
  have htmek : tme (fun j : Fin n => if j = k then M else 0) = M := by
    unfold tme; simp
  refine ⟨k, hk, ?_, ?_⟩
  · intro m hm htme
    obtain ⟨k', h1, h2, -⟩ := key m hm htme
    rw [hconc, ← hRk k' h1]; exact h2
  · intro m hm htme hmax i hi
    obtain ⟨k', h1, h2, h3⟩ := key m hm htme
    have hge := hmax _ hfeas htmek
    rw [hconc, ← hRk k' h1] at hge
    have heq := (h3.mp (le_antisymm h2 hge)) i hi.ne'
    intro j
    rw [heq]; exact h1 j
