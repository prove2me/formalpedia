-- Prove2me | solution 1 for BudgetAgg.NashChar.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:51:51.265737+00:00
-- url     : https://prove2.me/submissions/172a1589-445d-4fcc-b763-ed66e1330315

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Theorems.Thm_BudgetAgg_NashChar_lemma_2

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
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (h : IsCoreFairShare P q) (j : Fin m) :
    q.1 j = 0 ↔ ∀ i, (P i).1 j = 0 := by
  constructor
  · intro hq i
    by_contra hne
    have hp : 0 < (P i).1 j := lt_of_le_of_ne ((P i).2.1 j) (Ne.symm hne)
    have h1 := lemma_2 P q h i
    have h2 := nc_leontief_le (P i) q.1 j hp
    rw [hq, zero_div] at h2
    have hn : (0 : ℝ) < 1 / (n : ℝ) :=
      div_pos one_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n)))
    linarith
  · intro hp
    by_contra hq
    have hqpos : 0 < q.1 j := lt_of_le_of_ne (q.2.1 j) (Ne.symm hq)
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
    set ε := q.1 j with hε
    have hεm : 0 < ε / m := div_pos hqpos hm
    let f : Fin m → ℝ := fun k => q.1 k - (if k = j then ε else 0) + ε / m
    have hf1 : ∀ k, k ≠ j → f k = q.1 k + ε / m := by
      intro k hk; simp only [f, if_neg hk]; ring
    have hfmem : f ∈ stdSimplex ℝ (Fin m) := by
      refine ⟨fun k => ?_, ?_⟩
      · by_cases hk : k = j
        · subst hk; simp only [f, if_true]; rw [hε]; linarith
        · rw [hf1 k hk]; linarith [q.2.1 k]
      · simp only [f]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, q.2.2]
        simp [Finset.sum_ite_eq']
        field_simp
        ring
    let qs : stdSimplex ℝ (Fin m) := ⟨f, hfmem⟩
    apply nc_not_core P q qs _ h
    intro i
    apply nc_lt_leontief
    intro k hk
    have hkj : k ≠ j := by
      rintro rfl; rw [hp i] at hk; exact lt_irrefl _ hk
    show leontief (P i) q.1 < f k / (P i).1 k
    rw [hf1 k hkj]
    calc leontief (P i) q.1 ≤ q.1 k / (P i).1 k := nc_leontief_le _ _ k hk
      _ < (q.1 k + ε / m) / (P i).1 k := by
          apply div_lt_div_of_pos_right _ hk; linarith
