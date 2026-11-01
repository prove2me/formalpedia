-- Prove2me | solution 1 for BudgetAgg.NashChar.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:50:38.336288+00:00
-- url     : https://prove2.me/submissions/1fc7c698-2bc7-444a-b9be-a4f9e538fda2

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

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
    (h : IsCoreFairShare P q) : IsEfficient P q := by
  rintro ⟨q', hweak, i', hstrict⟩
  obtain ⟨j0, hpj0, hj0⟩ := nc_exists_crit (P i') q.1
  have hlt : q.1 j0 < q'.1 j0 := by
    have h1 := nc_leontief_le (P i') q'.1 j0 hpj0
    have h2 : q.1 j0 / (P i').1 j0 < q'.1 j0 / (P i').1 j0 := by linarith
    exact (div_lt_div_iff_of_pos_right hpj0).mp h2
  set ε := q'.1 j0 - q.1 j0 with hε
  have hεpos : 0 < ε := by linarith
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  have hεm : 0 < ε / m := div_pos hεpos hm
  let f : Fin m → ℝ := fun j => q'.1 j - (if j = j0 then ε else 0) + ε / m
  have hf0 : f j0 = q.1 j0 + ε / m := by simp only [f, if_true]; rw [hε]; ring
  have hf1 : ∀ j, j ≠ j0 → f j = q'.1 j + ε / m := by
    intro j hj; simp only [f, if_neg hj]; ring
  have hfmem : f ∈ stdSimplex ℝ (Fin m) := by
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = j0
      · subst hj; rw [hf0]; linarith [q.2.1 j]
      · rw [hf1 j hj]; linarith [q'.2.1 j]
    · simp only [f]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, q'.2.2]
      simp [Finset.sum_ite_eq']
      field_simp
      ring
  let qs : stdSimplex ℝ (Fin m) := ⟨f, hfmem⟩
  apply nc_not_core P q qs _ h
  intro i
  apply nc_lt_leontief
  intro k hk
  show leontief (P i) q.1 < f k / (P i).1 k
  by_cases hkj : k = j0
  · subst hkj
    rw [hf0]
    calc leontief (P i) q.1 ≤ q.1 k / (P i).1 k := nc_leontief_le _ _ k hk
      _ < (q.1 k + ε / m) / (P i).1 k := by
          apply div_lt_div_of_pos_right _ hk; linarith
  · rw [hf1 k hkj]
    calc leontief (P i) q.1 ≤ leontief (P i) q'.1 := hweak i
      _ ≤ q'.1 k / (P i).1 k := nc_leontief_le _ _ k hk
      _ < (q'.1 k + ε / m) / (P i).1 k := by
          apply div_lt_div_of_pos_right _ hk; linarith

