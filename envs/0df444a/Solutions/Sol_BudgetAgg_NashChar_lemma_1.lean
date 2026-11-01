-- Prove2me | solution 1 for BudgetAgg.NashChar.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:53:11.158321+00:00
-- url     : https://prove2.me/submissions/ede23ee9-aa40-4d2f-a0f3-506dd65192cc

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

theorem nc_leontief_nonneg {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : stdSimplex ℝ (Fin m)) :
    0 ≤ leontief p q.1 := by
  obtain ⟨k, hk, hke⟩ := nc_exists_crit p q.1
  rw [← hke]; exact div_nonneg (q.2.1 k) hk.le

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m)) :
    IsEfficient P q ↔ ∀ j, 0 < q.1 j → ∃ i, j ∈ crit (P i) q.1 := by
  constructor
  · intro heff j hqj
    by_contra hnc
    push_neg at hnc
    -- every agent valuing j has slack at j
    have hslack : ∀ i, (P i).1 j * leontief (P i) q.1 < q.1 j := by
      intro i
      rcases (lt_or_eq_of_le ((P i).2.1 j)) with hp | hp
      · have hle := nc_leontief_le (P i) q.1 j hp
        have hne : q.1 j / (P i).1 j ≠ leontief (P i) q.1 := by
          intro he; exact hnc i ((nc_mem_crit _ _ j).mpr ⟨hp, he⟩)
        have hlt : leontief (P i) q.1 < q.1 j / (P i).1 j := lt_of_le_of_ne hle (Ne.symm hne)
        rw [lt_div_iff₀ hp] at hlt; linarith
      · rw [← hp, zero_mul]; exact hqj
    set M := Finset.univ.sup' Finset.univ_nonempty (fun i => (P i).1 j * leontief (P i) q.1)
      with hM
    have hMlt : M < q.1 j := (Finset.sup'_lt_iff _).mpr (fun i _ => hslack i)
    have hM0 : 0 ≤ M := by
      have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
      exact le_trans (mul_nonneg ((P i0).2.1 j) (nc_leontief_nonneg _ q))
        (Finset.le_sup' (fun i => (P i).1 j * leontief (P i) q.1) (Finset.mem_univ i0))
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
    set δ := q.1 j - M with hδ
    have hδpos : 0 < δ := by linarith
    have hδm : 0 < δ / m := div_pos hδpos hm
    let f : Fin m → ℝ := fun k => q.1 k - (if k = j then δ else 0) + δ / m
    have hf0 : f j = M + δ / m := by simp only [f, if_true]; rw [hδ]; ring
    have hf1 : ∀ k, k ≠ j → f k = q.1 k + δ / m := by
      intro k hk; simp only [f, if_neg hk]; ring
    have hfmem : f ∈ stdSimplex ℝ (Fin m) := by
      refine ⟨fun k => ?_, ?_⟩
      · by_cases hk : k = j
        · subst hk; rw [hf0]; linarith
        · rw [hf1 k hk]; linarith [q.2.1 k]
      · simp only [f]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, q.2.2]
        simp [Finset.sum_ite_eq']
        field_simp
        ring
    let qs : stdSimplex ℝ (Fin m) := ⟨f, hfmem⟩
    have himp : ∀ i, leontief (P i) q.1 < leontief (P i) qs.1 := by
      intro i
      apply nc_lt_leontief
      intro k hk
      show leontief (P i) q.1 < f k / (P i).1 k
      by_cases hkj : k = j
      · subst hkj
        rw [hf0, lt_div_iff₀ hk]
        have : (P i).1 k * leontief (P i) q.1 ≤ M :=
          Finset.le_sup' (fun i => (P i).1 k * leontief (P i) q.1) (Finset.mem_univ i)
        linarith
      · rw [hf1 k hkj]
        calc leontief (P i) q.1 ≤ q.1 k / (P i).1 k := nc_leontief_le _ _ k hk
          _ < (q.1 k + δ / m) / (P i).1 k := by
              apply div_lt_div_of_pos_right _ hk; linarith
    apply heff
    have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    exact ⟨qs, fun i => (himp i).le, i0, himp i0⟩
  · intro hcrit
    rintro ⟨q', hweak, i', hstrict⟩
    obtain ⟨j0, hpj0, hj0⟩ := nc_exists_crit (P i') q.1
    have hlt : q.1 j0 < q'.1 j0 := by
      have h1 := nc_leontief_le (P i') q'.1 j0 hpj0
      have h2 : q.1 j0 / (P i').1 j0 < q'.1 j0 / (P i').1 j0 := by linarith
      exact (div_lt_div_iff_of_pos_right hpj0).mp h2
    -- some alternative loses mass
    have hex : ∃ k, q'.1 k < q.1 k := by
      by_contra hno
      push_neg at hno
      have hs : ∑ k, q.1 k < ∑ k, q'.1 k :=
        Finset.sum_lt_sum (fun k _ => hno k) ⟨j0, Finset.mem_univ _, hlt⟩
      rw [q.2.2, q'.2.2] at hs
      exact lt_irrefl _ hs
    obtain ⟨k, hk⟩ := hex
    have hqk : 0 < q.1 k := lt_of_le_of_lt (q'.2.1 k) hk
    obtain ⟨i, hi⟩ := hcrit k hqk
    obtain ⟨hp, he⟩ := (nc_mem_crit _ _ k).mp hi
    have h1 := nc_leontief_le (P i) q'.1 k hp
    have h2 : q'.1 k / (P i).1 k < q.1 k / (P i).1 k := div_lt_div_of_pos_right hk hp
    have h3 := hweak i
    linarith
