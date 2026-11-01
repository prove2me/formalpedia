-- Prove2me | solution 1 for BudgetAgg.NashChar.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:55:42.174783+00:00
-- url     : https://prove2.me/submissions/43d540b5-6bb4-4e70-abdf-54cd6d242b03

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Theorems.Thm_BudgetAgg_NashChar_lemma_1

open BudgetAgg.NashChar

theorem nc_leontief_le {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (k : Fin m)
    (hk : 0 < p.1 k) : leontief p q ≤ q k / p.1 k := by
  unfold leontief
  exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)

theorem nc_lt_leontief {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (c : ℝ)
    (h : ∀ k, 0 < p.1 k → c < q k / p.1 k) : c < leontief p q := by
  unfold leontief
  rw [Finset.lt_inf'_iff]
  intro k hk
  exact h k (Finset.mem_filter.mp hk).2

theorem nc_exists_crit {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) :
    ∃ k, 0 < p.1 k ∧ q k / p.1 k = leontief p q := by
  unfold leontief
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_inf' (positive_support_nonempty p)
    (fun j => q j / p.1 j)
  exact ⟨k, (Finset.mem_filter.mp hk).2, he.symm⟩

theorem nc_mem_crit {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (k : Fin m) :
    k ∈ crit p q ↔ 0 < p.1 k ∧ q k / p.1 k = leontief p q := by
  unfold crit
  simp [Finset.mem_filter]

/-- A distribution that makes every agent strictly better off violates core fair share
(take the grand coalition). -/
theorem nc_not_core {n m : ℕ} [NeZero n] (P : Profile n m) (q qs : stdSimplex ℝ (Fin m))
    (h : ∀ i, leontief (P i) q.1 < leontief (P i) qs.1) : ¬ IsCoreFairShare P q := by
  intro hc
  apply hc Finset.univ Finset.univ_nonempty
  refine ⟨qs, fun q'' i _ => ?_⟩
  have hn : ((Finset.univ : Finset (Fin n)).card : ℝ) / (n : ℝ) = 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hf : (fun j => ((Finset.univ : Finset (Fin n)).card : ℝ) / (n : ℝ) * qs.1 j +
      (1 - ((Finset.univ : Finset (Fin n)).card : ℝ) / (n : ℝ)) * q''.1 j) = qs.1 := by
    funext j; rw [hn]; ring
  rw [hf]
  exact h i

theorem nc_leontief_le_one {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : stdSimplex ℝ (Fin m)) :
    leontief p q.1 ≤ 1 := by
  have h : ∀ k, p.1 k * leontief p q.1 ≤ q.1 k := by
    intro k
    rcases lt_or_eq_of_le (p.2.1 k) with hp | hp
    · have := nc_leontief_le p q.1 k hp
      rw [le_div_iff₀ hp] at this; linarith
    · rw [← hp, zero_mul]; exact q.2.1 k
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => h k)
  rw [← Finset.sum_mul, p.2.2, q.2.2, one_mul] at hs
  exact hs

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hq : IsEfficient P q) (j : Fin m) :
    q.1 j ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => (P i).1 j) := by
  rcases lt_or_eq_of_le (q.2.1 j) with hqj | hqj
  · obtain ⟨i, hi⟩ := (lemma_1 P q).mp hq j hqj
    obtain ⟨hp, he⟩ := (nc_mem_crit _ _ j).mp hi
    have h1 := nc_leontief_le_one (P i) q
    have h2 : q.1 j = (P i).1 j * leontief (P i) q.1 := by
      rw [← he]; field_simp
    have h3 : (P i).1 j ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => (P i).1 j) :=
      Finset.le_sup' (fun i => (P i).1 j) (Finset.mem_univ i)
    rw [h2]
    nlinarith
  · rw [← hqj]
    have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    exact le_trans ((P i0).2.1 j) (Finset.le_sup' (fun i => (P i).1 j) (Finset.mem_univ i0))
