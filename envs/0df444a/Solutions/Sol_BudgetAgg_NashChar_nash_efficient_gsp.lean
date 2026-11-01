-- Prove2me | solution 1 for BudgetAgg.NashChar.nash_efficient_gsp
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:09:50.060555+00:00
-- url     : https://prove2.me/submissions/0864212e-1c87-4b7e-9053-dcdda9036705

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Theorems.Thm_BudgetAgg_NashChar_lemma_6

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

theorem nc_leontief_nonneg {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : stdSimplex ℝ (Fin m)) :
    0 ≤ leontief p q.1 := by
  obtain ⟨k, hk, hke⟩ := nc_exists_crit p q.1
  rw [← hke]; exact div_nonneg (q.2.1 k) hk.le

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

theorem nc_nash_eff {n m : ℕ} [NeZero m] (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hq : IsNashOutcome P q.1) : IsEfficient P q := by
  rintro ⟨q', hweak, i', hstrict⟩
  have hlt : nashProduct P q.1 < nashProduct P q'.1 :=
    Finset.prod_lt_prod (fun i _ => nc_nash_pos P q hq i) (fun i _ => hweak i)
      ⟨i', Finset.mem_univ _, hstrict⟩
  have := hq.2 q'.1 q'.2
  linarith

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (g : Mechanism n m) (hg : ∀ P, IsNashOutcome P (g P).1) :
    (∀ P, IsEfficient P (g P)) ∧ IsGroupSP g := by
  classical
  refine ⟨fun P => nc_nash_eff P (g P) (hg P), ?_⟩
  intro S P P' hout
  by_cases hlose : ∃ i ∈ S, leontief (P i) (g P').1 < leontief (P i) (g P).1
  · exact Or.inl hlose
  right
  push_neg at hlose
  set q := g P with hq
  set q' := g P' with hq'
  by_cases hqq : q = q'
  · intro i _; rw [hqq]
  exfalso
  -- some alternative gains
  obtain ⟨y, hy⟩ : ∃ y, q.1 y < q'.1 y := by
    by_contra h
    push_neg at h
    have hsum : ∑ j, q'.1 j = ∑ j, q.1 j := by rw [q.2.2, q'.2.2]
    have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => h j)).mp hsum
    exact hqq (Subtype.ext (funext fun j => (heq j (Finset.mem_univ j)).symm))
  set G := Finset.univ.filter (fun i => leontief (P i) q.1 ≤ leontief (P i) q'.1) with hG
  have hSG : ∀ i ∈ S, i ∈ G := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlose i hi⟩
  -- critical alternatives of non-losing agents do not shrink
  have hcritG : ∀ x ∈ critG P q.1 G, q.1 x ≤ q'.1 x := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hp, he⟩ := (nc_mem_crit _ _ x).mp hxi
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := nc_leontief_le (P i) q'.1 x hp
    have : q.1 x / (P i).1 x ≤ q'.1 x / (P i).1 x := by rw [he]; linarith
    exact (div_le_div_iff_of_pos_right hp).mp this
  set B := insert y (critG P q.1 G) with hB
  have hBle : ∀ x ∈ B, q.1 x ≤ q'.1 x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hy.le
    · exact hcritG x h
  have hBlt : ∑ x ∈ B, q.1 x < ∑ x ∈ B, q'.1 x :=
    Finset.sum_lt_sum hBle ⟨y, Finset.mem_insert_self _ _, hy⟩
  obtain ⟨s, ⟨hs0, hscol, hsrow⟩, hsupp⟩ := (lemma_6 P q).mp (hg P)
  obtain ⟨s', ⟨hs0', hscol', hsrow'⟩, hsupp'⟩ := (lemma_6 P' q').mp (hg P')
  have e1 : ∑ x ∈ B, q.1 x = ∑ i, ∑ x ∈ B, s i x := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun x _ => (hscol x).symm)
  have e2 : ∑ x ∈ B, q'.1 x = ∑ i, ∑ x ∈ B, s' i x := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun x _ => (hscol' x).symm)
  rw [e1, e2] at hBlt
  obtain ⟨j, _, hj⟩ := Finset.exists_lt_of_sum_lt hBlt
  -- j is not in G
  have hjG : j ∉ G := by
    intro hjG
    have hfull : ∑ x ∈ B, s j x = 1 / (n : ℝ) := by
      rw [← hsrow j]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      apply hsupp
      intro hxc
      exact hx (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j, hjG, hxc⟩))
    have hle : ∑ x ∈ B, s' j x ≤ 1 / (n : ℝ) := by
      rw [← hsrow' j]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ => hs0' j x)
    linarith
  have hjS : j ∉ S := fun h => hjG (hSG j h)
  have hPj : P' j = P j := hout j hjS
  -- j puts positive mass on some x ∈ B in the decomposition of q'
  obtain ⟨x, hxB, hx⟩ : ∃ x ∈ B, 0 < s' j x := by
    by_contra h
    push_neg at h
    have h1 : ∑ x ∈ B, s' j x ≤ 0 := Finset.sum_nonpos h
    have h2 : 0 ≤ ∑ x ∈ B, s j x := Finset.sum_nonneg (fun x _ => hs0 j x)
    linarith
  have hxc : x ∈ crit (P' j) q'.1 := by
    by_contra hc; rw [hsupp' j x hc] at hx; exact lt_irrefl _ hx
  rw [hPj] at hxc
  obtain ⟨hp, he⟩ := (nc_mem_crit _ _ x).mp hxc
  have h1 := nc_leontief_le (P j) q.1 x hp
  have h2 : q.1 x / (P j).1 x ≤ q'.1 x / (P j).1 x :=
    div_le_div_of_nonneg_right (hBle x hxB) hp.le
  apply hjG
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← he]; linarith⟩
