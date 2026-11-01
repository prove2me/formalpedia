-- Prove2me | solution 1 for BudgetAgg.NashChar.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:51:50.705087+00:00
-- url     : https://prove2.me/submissions/a56f6fee-8974-4a57-898e-c18903f1163b

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
    (h : ∀ G : Finset (Fin n), (G.card : ℝ) / (n : ℝ) ≤ ∑ j ∈ critG P q.1 G, q.1 j) :
    IsCoreFairShare P q := by
  intro S hS ⟨q', hblock⟩
  set c : ℝ := (S.card : ℝ) / (n : ℝ) with hc
  set T := critG P q.1 S with hT
  -- every alternative critical for a member of S strictly gains in every mixture
  have key : ∀ q'' : stdSimplex ℝ (Fin m), ∀ j ∈ T, q.1 j < c * q'.1 j + (1 - c) * q''.1 j := by
    intro q'' j hj
    obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨hp, heq⟩ := (nc_mem_crit (P i) q.1 j).mp hji
    have h1 := hblock q'' i hi
    have h2 := nc_leontief_le (P i) (fun j => c * q'.1 j + (1 - c) * q''.1 j) j hp
    rw [← heq] at h1
    exact (div_lt_div_iff_of_pos_right hp).mp (lt_of_lt_of_le h1 h2)
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := hS
    obtain ⟨k, hk, hke⟩ := nc_exists_crit (P i) q.1
    exact ⟨k, Finset.mem_biUnion.mpr ⟨i, hi, (nc_mem_crit _ _ k).mpr ⟨hk, hke⟩⟩⟩
  by_cases hall : ∀ k, k ∈ T
  · -- T = M: summing over all alternatives gives 1 < 1
    have hTu : T = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    have hs := Finset.sum_lt_sum_of_nonempty hTne (key q')
    rw [hTu, q.2.2] at hs
    have : ∑ j, (c * q'.1 j + (1 - c) * q'.1 j) = 1 := by
      have : ∀ j, c * q'.1 j + (1 - c) * q'.1 j = q'.1 j := fun j => by ring
      simp only [this]; exact q'.2.2
    linarith
  · push_neg at hall
    obtain ⟨k, hk⟩ := hall
    let e : stdSimplex ℝ (Fin m) := ⟨Pi.single k 1, single_mem_stdSimplex ℝ k⟩
    have hs := Finset.sum_lt_sum_of_nonempty hTne (key e)
    have he : ∀ j ∈ T, c * q'.1 j + (1 - c) * e.1 j = c * q'.1 j := by
      intro j hj
      have hjk : j ≠ k := fun h => hk (h ▸ hj)
      simp [e, Pi.single_apply, hjk]
    rw [Finset.sum_congr rfl he, ← Finset.mul_sum] at hs
    have hle : ∑ j ∈ T, q'.1 j ≤ 1 := by
      rw [← q'.2.2]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => q'.2.1 j)
    have hc0 : 0 ≤ c := by positivity
    have := h S
    nlinarith
