-- Prove2me | solution 1 for BudgetAgg.NashChar.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:09:50.70044+00:00
-- url     : https://prove2.me/submissions/8f1e1f92-9c3e-40c5-94df-024649d10516

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Theorems.Thm_BudgetAgg_NashChar_lemma_6
import Theorems.Thm_BudgetAgg_NashChar_nash_unique

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

/-- The support condition of Lemma 6, rewritten as a closed (polynomial) condition. -/
theorem nc_crit_iff_cross {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : stdSimplex ℝ (Fin m))
    (j : Fin m) (hqj : 0 < q.1 j) :
    j ∈ crit p q.1 ↔ ∀ k, q.1 j * p.1 k ≤ q.1 k * p.1 j := by
  constructor
  · intro hj k
    obtain ⟨hp, he⟩ := (nc_mem_crit _ _ j).mp hj
    rcases lt_or_eq_of_le (p.2.1 k) with hk | hk
    · have h1 := nc_leontief_le p q.1 k hk
      rw [← he, div_le_div_iff₀ hp hk] at h1
      linarith
    · rw [← hk, mul_zero]; exact mul_nonneg (q.2.1 k) (p.2.1 j)
  · intro h
    have hp : 0 < p.1 j := by
      by_contra hp
      have hp0 : p.1 j = 0 := le_antisymm (not_lt.mp hp) (p.2.1 j)
      have : ∀ k, q.1 j * p.1 k ≤ 0 := fun k => by have := h k; rw [hp0, mul_zero] at this; exact this
      have hs : ∑ k, q.1 j * p.1 k ≤ 0 := Finset.sum_nonpos (fun k _ => this k)
      rw [← Finset.mul_sum, p.2.2, mul_one] at hs
      linarith
    rw [nc_mem_crit]
    refine ⟨hp, le_antisymm ?_ (nc_leontief_le p q.1 j hp)⟩
    unfold leontief
    rw [Finset.le_inf'_iff]
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    rw [div_le_div_iff₀ hp hk']
    linarith [h k]

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (g : Mechanism n m) (hg : ∀ P, IsNashOutcome P (g P).1) :
    Continuous g := by
  classical
  set Z := Set.Icc (0 : Fin n → Fin m → ℝ) 1
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp isCompact_Icc
  -- the closed set of (profile, distribution, decomposition) triples
  set Cset : Set ((Profile n m × stdSimplex ℝ (Fin m)) × Z) :=
    {w | (∀ i j, 0 ≤ (w.2 : Fin n → Fin m → ℝ) i j) ∧
      (∀ j, ∑ i, (w.2 : Fin n → Fin m → ℝ) i j = (w.1.2 : Fin m → ℝ) j) ∧
      (∀ i, ∑ j, (w.2 : Fin n → Fin m → ℝ) i j = 1 / (n : ℝ)) ∧
      ∀ i j k, (w.2 : Fin n → Fin m → ℝ) i j *
        ((w.1.2 : Fin m → ℝ) j * ((w.1.1 i : Fin m → ℝ) k) -
          (w.1.2 : Fin m → ℝ) k * ((w.1.1 i : Fin m → ℝ) j)) ≤ 0} with hCset
  have hS : ∀ i j, Continuous (fun w : (Profile n m × stdSimplex ℝ (Fin m)) × Z =>
      (w.2 : Fin n → Fin m → ℝ) i j) := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))
  have hQ : ∀ j, Continuous (fun w : (Profile n m × stdSimplex ℝ (Fin m)) × Z =>
      (w.1.2 : Fin m → ℝ) j) := fun j =>
    (continuous_apply j).comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
  have hPc : ∀ i k, Continuous (fun w : (Profile n m × stdSimplex ℝ (Fin m)) × Z =>
      (w.1.1 i : Fin m → ℝ) k) := fun i k =>
    (continuous_apply k).comp (continuous_subtype_val.comp
      ((continuous_apply i).comp (continuous_fst.comp continuous_fst)))
  have hCclosed : IsClosed Cset := by
    simp only [hCset, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
      (IsClosed.inter (isClosed_iInter fun j => ?_)
        (IsClosed.inter (isClosed_iInter fun i => ?_)
          (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k => ?_)))
    · exact isClosed_le continuous_const (hS i j)
    · exact isClosed_eq (continuous_finset_sum _ fun i _ => hS i j) (hQ j)
    · exact isClosed_eq (continuous_finset_sum _ fun j _ => hS i j) continuous_const
    · exact isClosed_le ((hS i j).mul (((hQ j).mul (hPc i k)).sub ((hQ k).mul (hPc i j))))
        continuous_const
  -- Nash outcomes are exactly the projections of Cset
  have hNash : ∀ (P : Profile n m) (q : stdSimplex ℝ (Fin m)),
      IsNashOutcome P q.1 ↔ ∃ z : Z, ((P, q), z) ∈ Cset := by
    intro P q
    constructor
    · intro hq
      obtain ⟨s, ⟨hs0, hscol, hsrow⟩, hsupp⟩ := (lemma_6 P q).mp hq
      have hs1 : ∀ i j, s i j ≤ 1 := by
        intro i j
        have h1 : s i j ≤ ∑ k, s i k := Finset.single_le_sum (fun k _ => hs0 i k) (Finset.mem_univ j)
        rw [hsrow i] at h1
        have : 1 / (n : ℝ) ≤ 1 := by
          rw [div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n)))]
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
        linarith
      refine ⟨⟨s, fun i j => hs0 i j, fun i j => hs1 i j⟩, hs0, hscol, hsrow, ?_⟩
      intro i j k
      show s i j * (q.1 j * (P i).1 k - q.1 k * (P i).1 j) ≤ 0
      rcases lt_or_eq_of_le (hs0 i j) with h | h
      · have hqj : 0 < q.1 j := by
          rw [← hscol j]
          exact lt_of_lt_of_le h (Finset.single_le_sum (fun a _ => hs0 a j) (Finset.mem_univ i))
        have hc : j ∈ crit (P i) q.1 := by
          by_contra hc; rw [hsupp i j hc] at h; exact lt_irrefl _ h
        have := (nc_crit_iff_cross (P i) q j hqj).mp hc k
        exact mul_nonpos_of_nonneg_of_nonpos h.le (by linarith)
      · rw [← h, zero_mul]
    · rintro ⟨⟨s, _⟩, hs0, hscol, hsrow, hcross⟩
      have hs0 : ∀ i j, 0 ≤ s i j := hs0
      have hscol : ∀ j, ∑ i, s i j = q.1 j := hscol
      have hsrow : ∀ i, ∑ j, s i j = 1 / (n : ℝ) := hsrow
      have hcross : ∀ i j k, s i j * (q.1 j * (P i).1 k - q.1 k * (P i).1 j) ≤ 0 := hcross
      refine (lemma_6 P q).mpr ⟨s, ⟨hs0, hscol, hsrow⟩, fun i j hj => ?_⟩
      by_contra hne
      have h : 0 < s i j := lt_of_le_of_ne (hs0 i j) (Ne.symm hne)
      have hqj : 0 < q.1 j := by
        rw [← hscol j]
        exact lt_of_lt_of_le h (Finset.single_le_sum (fun a _ => hs0 a j) (Finset.mem_univ i))
      apply hj
      rw [nc_crit_iff_cross (P i) q j hqj]
      intro k
      have := hcross i j k
      have h2 : q.1 j * (P i).1 k - q.1 k * (P i).1 j ≤ 0 := by
        by_contra h3; push_neg at h3
        have := mul_pos h h3; linarith
      linarith
  -- the graph of g is closed
  have hgraph : {x : Profile n m × stdSimplex ℝ (Fin m) | x.2 = g x.1} = Prod.fst '' Cset := by
    ext ⟨P, q⟩
    simp only [Set.mem_setOf_eq, Set.mem_image, Prod.exists]
    constructor
    · intro h
      obtain ⟨z, hz⟩ := (hNash P q).mp (h ▸ hg P)
      exact ⟨P, q, z, hz, rfl⟩
    · rintro ⟨P', q', z, hz, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hq := (hNash P' q').mpr ⟨z, hz⟩
      obtain ⟨q0, _, huniq⟩ := nash_unique P'
      rw [huniq q' hq, huniq (g P') (hg P')]
  have hgc : IsClosed {x : Profile n m × stdSimplex ℝ (Fin m) | x.2 = g x.1} := by
    rw [hgraph]; exact isClosedMap_fst_of_compactSpace _ hCclosed
  rw [continuous_iff_isClosed]
  intro C hC
  have : g ⁻¹' C = Prod.fst '' ({x : Profile n m × stdSimplex ℝ (Fin m) | x.2 = g x.1} ∩
      (Set.univ ×ˢ C)) := by
    ext P
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_prod, Set.mem_univ, true_and, Prod.exists, exists_and_right, exists_eq_right]
    constructor
    · intro h; exact ⟨g P, rfl, h⟩
    · rintro ⟨q, hq, hC'⟩; rw [← hq]; exact hC'
  rw [this]
  exact isClosedMap_fst_of_compactSpace _ (hgc.inter (isClosed_univ.prod hC))
