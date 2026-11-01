-- Prove2me | solution 1 for BudgetAgg.NashChar.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:55:41.550122+00:00
-- url     : https://prove2.me/submissions/db352e80-d71c-4d83-89f2-6d1dce1634d7

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

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q q' : stdSimplex ℝ (Fin m))
    (hq : IsEfficient P q) (hq' : IsEfficient P q')
    (hu : ∀ i, leontief (P i) q.1 = leontief (P i) q'.1) : q = q' := by
  have hcrit := (lemma_1 P q).mp hq
  have hle : ∀ j, q.1 j ≤ q'.1 j := by
    intro j
    by_contra hlt
    push_neg at hlt
    have hqj : 0 < q.1 j := lt_of_le_of_lt (q'.2.1 j) hlt
    obtain ⟨i, hi⟩ := hcrit j hqj
    obtain ⟨hp, he⟩ := (nc_mem_crit _ _ j).mp hi
    have h1 := nc_leontief_le (P i) q'.1 j hp
    have h2 : q'.1 j / (P i).1 j < q.1 j / (P i).1 j := div_lt_div_of_pos_right hlt hp
    have h3 := hu i
    linarith
  have hsum : ∑ j, q.1 j = ∑ j, q'.1 j := by rw [q.2.2, q'.2.2]
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum
  exact Subtype.ext (funext fun j => heq j (Finset.mem_univ j))
