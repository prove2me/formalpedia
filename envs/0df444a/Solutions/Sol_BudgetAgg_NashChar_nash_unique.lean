-- Prove2me | solution 1 for BudgetAgg.NashChar.nash_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:57:43.360008+00:00
-- url     : https://prove2.me/submissions/c9bb5758-3584-4d49-a98e-22fde2cd987c

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Theorems.Thm_BudgetAgg_NashChar_lemma_7

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

theorem nc_le_leontief {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (c : ℝ)
    (h : ∀ k, 0 < p.1 k → c ≤ q k / p.1 k) : c ≤ leontief p q := by
  unfold leontief
  rw [Finset.le_inf'_iff]
  intro k hk
  exact h k (Finset.mem_filter.mp hk).2

theorem nc_leontief_nonneg {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : stdSimplex ℝ (Fin m)) :
    0 ≤ leontief p q.1 := by
  obtain ⟨k, hk, hke⟩ := nc_exists_crit p q.1
  rw [← hke]; exact div_nonneg (q.2.1 k) hk.le

theorem nc_leontief_cont {m : ℕ} (p : stdSimplex ℝ (Fin m)) :
    Continuous (fun q : Fin m → ℝ => leontief p q) := by
  unfold leontief
  apply Continuous.finset_inf'_apply
  intro j _
  exact (continuous_apply j).div_const _

theorem nc_unif_mem (m : ℕ) [NeZero m] :
    (fun _ : Fin m => 1 / (m : ℝ)) ∈ stdSimplex ℝ (Fin m) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  refine ⟨fun _ => by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem nc_unif_pos {m : ℕ} [NeZero m] (p : stdSimplex ℝ (Fin m)) :
    0 < leontief p (fun _ : Fin m => 1 / (m : ℝ)) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  apply nc_lt_leontief
  intro k hk
  positivity

/-- A Nash outcome gives every agent positive utility. -/
theorem nc_nash_pos {n m : ℕ} [NeZero m] (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hq : IsNashOutcome P q.1) (i : Fin n) : 0 < leontief (P i) q.1 := by
  have hu := hq.2 _ (nc_unif_mem m)
  have hpos : 0 < nashProduct P (fun _ : Fin m => 1 / (m : ℝ)) :=
    Finset.prod_pos (fun i _ => nc_unif_pos (P i))
  have hprod : 0 < nashProduct P q.1 := lt_of_lt_of_le hpos hu
  rcases lt_or_eq_of_le (nc_leontief_nonneg (P i) q) with h | h
  · exact h
  · exfalso
    have : nashProduct P q.1 = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h.symm
    linarith

/-- A Nash outcome is efficient. -/
theorem nc_nash_eff {n m : ℕ} [NeZero m] (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hq : IsNashOutcome P q.1) : IsEfficient P q := by
  rintro ⟨q', hweak, i', hstrict⟩
  have hlt : nashProduct P q.1 < nashProduct P q'.1 :=
    Finset.prod_lt_prod (fun i _ => nc_nash_pos P q hq i) (fun i _ => hweak i)
      ⟨i', Finset.mem_univ _, hstrict⟩
  have := hq.2 q'.1 q'.2
  linarith

theorem solution {n m : ℕ} [NeZero n] [NeZero m] (P : Profile n m) :
    ∃! q : stdSimplex ℝ (Fin m), IsNashOutcome P q.1 := by
  have hcont : Continuous (nashProduct P) := by
    unfold nashProduct
    exact continuous_finset_prod _ (fun i _ => nc_leontief_cont (P i))
  obtain ⟨q0, hq0, hmax⟩ := (isCompact_stdSimplex ℝ (Fin m)).exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ (0 : Fin m)⟩ hcont.continuousOn
  have hN0 : IsNashOutcome P q0 := ⟨hq0, fun q' hq' => hmax hq'⟩
  refine ⟨⟨q0, hq0⟩, hN0, ?_⟩
  intro y hy
  set x : stdSimplex ℝ (Fin m) := ⟨q0, hq0⟩
  have hx : IsNashOutcome P x.1 := hN0
  -- equal utilities
  have hequ : ∀ i, leontief (P i) y.1 = leontief (P i) x.1 := by
    by_contra hne
    push_neg at hne
    obtain ⟨i0, hi0⟩ := hne
    let w : Fin m → ℝ := fun j => (y.1 j + x.1 j) / 2
    have hw : w ∈ stdSimplex ℝ (Fin m) := by
      refine ⟨fun j => ?_, ?_⟩
      · have := y.2.1 j; have := x.2.1 j; simp only [w]; linarith
      · simp only [w]
        rw [← Finset.sum_div, Finset.sum_add_distrib, y.2.2, x.2.2]; norm_num
    have hconc : ∀ i, (leontief (P i) y.1 + leontief (P i) x.1) / 2 ≤ leontief (P i) w := by
      intro i
      apply nc_le_leontief
      intro k hk
      have h1 := nc_leontief_le (P i) y.1 k hk
      have h2 := nc_leontief_le (P i) x.1 k hk
      have : w k / (P i).1 k = (y.1 k / (P i).1 k + x.1 k / (P i).1 k) / 2 := by
        simp only [w]; field_simp
      rw [this]; linarith
    set a := fun i => leontief (P i) y.1
    set b := fun i => leontief (P i) x.1
    have ha : ∀ i, 0 < a i := fun i => nc_nash_pos P y hy i
    have hb : ∀ i, 0 < b i := fun i => nc_nash_pos P x hx i
    have hVa : nashProduct P y.1 = ∏ i, a i := rfl
    have hVb : nashProduct P x.1 = ∏ i, b i := rfl
    have hab : ∏ i, a i = ∏ i, b i := by
      have h1 := hy.2 x.1 x.2
      have h2 := hx.2 y.1 y.2
      rw [hVa, hVb] at *; linarith
    have hstrict : ∏ i, (a i * b i) < ∏ i, ((a i + b i) / 2) ^ 2 := by
      apply Finset.prod_lt_prod (fun i _ => mul_pos (ha i) (hb i))
      · intro i _; nlinarith [sq_nonneg (a i - b i)]
      · refine ⟨i0, Finset.mem_univ _, ?_⟩
        have : a i0 - b i0 ≠ 0 := sub_ne_zero.mpr hi0
        have := sq_pos_of_ne_zero this
        nlinarith
    have hle : ∏ i, ((a i + b i) / 2) ^ 2 ≤ ∏ i, (leontief (P i) w) ^ 2 := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _
        have := hconc i
        have h0 : 0 ≤ (a i + b i) / 2 := by have := ha i; have := hb i; positivity
        exact pow_le_pow_left₀ h0 this 2
    rw [Finset.prod_mul_distrib, ← hab, Finset.prod_pow] at hstrict
    simp only [Finset.prod_pow] at hle
    have hwle : nashProduct P w ≤ ∏ i, a i := by
      have := hy.2 w hw; rw [hVa] at this; exact this
    have hApos : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
    have hWnn : 0 ≤ nashProduct P w := by
      unfold nashProduct
      exact Finset.prod_nonneg (fun i _ => le_trans (by have := ha i; have := hb i; positivity)
        (hconc i))
    have : (∏ i, a i) * (∏ i, a i) < (nashProduct P w) ^ 2 := by
      unfold nashProduct; linarith
    nlinarith
  exact lemma_7 P y x (nc_nash_eff P y hy) (nc_nash_eff P x hx) hequ
