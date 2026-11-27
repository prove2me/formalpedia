-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:32.661028+00:00
-- url     : https://prove2.me/submissions/8155510b-d13b-4f0e-98e0-e4c233e5f61f

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Lemma 14, p. 40: with Leximin-Leontief preferences, `q` is efficient iff every
alternative it funds is critical (minimum ratio) for some agent. -/
theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m)) :
    IsLexEfficient P q ↔ ∀ j, 0 < q.1 j → ∃ i, j ∈ crit (P i) q.1 := by
      have key : ∀ (L1 L2 : List ℝ) (x : ℝ), List.Pairwise (· ≤ ·) L1 → x ∈ L1 → L2 ≠ [] →
          (∀ y ∈ L2, x < y) → List.Lex (· < ·) L1 L2 := by
        intro L1 L2 x hs hx hne hlt
        cases L1 with
        | nil => simp at hx
        | cons a t =>
          cases L2 with
          | nil => exact absurd rfl hne
          | cons b s =>
            apply List.Lex.rel
            have hax : a ≤ x := by
              rcases List.mem_cons.mp hx with h | h
              · exact h ▸ le_refl a
              · exact (List.pairwise_cons.mp hs).1 x h
            exact lt_of_le_of_lt hax (hlt b List.mem_cons_self)
      have memR : ∀ (p : stdSimplex ℝ (Fin m)) (f : Fin m → ℝ) (y : ℝ),
          y ∈ ratioList p f ↔ ∃ k, 0 < p.1 k ∧ f k / p.1 k = y := by
        intro p f y
        unfold ratioList
        rw [Multiset.mem_sort, Multiset.mem_map]
        simp [Finset.mem_filter]
      have sortedR : ∀ (p : stdSimplex ℝ (Fin m)) (f : Fin m → ℝ),
          List.Pairwise (· ≤ ·) (ratioList p f) := by
        intro p f
        exact Multiset.pairwise_sort _ _
      have neR : ∀ (p : stdSimplex ℝ (Fin m)) (f : Fin m → ℝ), ratioList p f ≠ [] := by
        intro p f h
        obtain ⟨k, hk⟩ := positive_support_nonempty p
        have : f k / p.1 k ∈ ratioList p f :=
          (memR p f _).mpr ⟨k, (Finset.mem_filter.mp hk).2, rfl⟩
        rw [h] at this
        simp at this
      have leR : ∀ (p : stdSimplex ℝ (Fin m)) (f : Fin m → ℝ) (k : Fin m), 0 < p.1 k →
          leontief p f ≤ f k / p.1 k := by
        intro p f k hk
        exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)
      have minR : ∀ (p : stdSimplex ℝ (Fin m)) (f : Fin m → ℝ), leontief p f ∈ ratioList p f := by
        intro p f
        obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_inf' (positive_support_nonempty p)
          (fun j => f j / p.1 j)
        exact (memR p f _).mpr ⟨k, (Finset.mem_filter.mp hk).2, he.symm⟩
      have asymmL : ∀ (L1 L2 : List ℝ), List.Lex (· < ·) L1 L2 → List.Lex (· < ·) L2 L1 → False := by
        intro L1 L2 h1 h2
        exact List.lt_asymm (List.lex_lt.mp h1) (List.lex_lt.mp h2)
      have irrL : ∀ (L : List ℝ), List.Lex (· < ·) L L → False := by
        intro L h
        exact List.lt_irrefl L (List.lex_lt.mp h)
      constructor
      · intro hE j hj
        by_contra hcon
        push Not at hcon
        apply hE
        set L : Fin n → ℝ := fun i => leontief (P i) q.1 with hLdef
        set gap : Fin n → ℝ := fun i => q.1 j - L i * (P i).1 j with hgapdef
        have hL0 : ∀ i, 0 ≤ L i := by
          intro i
          apply Finset.le_inf'
          intro k hk
          exact div_nonneg (q.2.1 k) (le_of_lt (Finset.mem_filter.mp hk).2)
        have hgap : ∀ i, 0 < gap i := by
          intro i
          simp only [hgapdef]
          by_cases hp : 0 < (P i).1 j
          · have h1 : L i ≤ q.1 j / (P i).1 j := leR (P i) q.1 j hp
            have h2 : q.1 j / (P i).1 j ≠ L i := by
              intro h
              apply hcon i
              unfold crit
              rw [Finset.mem_filter, Finset.mem_filter]
              exact ⟨⟨Finset.mem_univ j, hp⟩, h⟩
            have h3 : L i < q.1 j / (P i).1 j := lt_of_le_of_ne h1 (Ne.symm h2)
            rw [lt_div_iff₀ hp] at h3
            linarith
          · have : (P i).1 j = 0 := le_antisymm (not_lt.mp hp) ((P i).2.1 j)
            rw [this]; simpa using hj
        set g : ℝ := Finset.univ.inf' Finset.univ_nonempty gap with hgdef
        have hg : 0 < g := (Finset.lt_inf'_iff _).mpr (fun i _ => hgap i)
        have hgle : ∀ i, g ≤ gap i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
        have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_neZero m
        set δ : ℝ := g / (2 * m) with hδdef
        have hδ : 0 < δ := by positivity
        have hmδ : (m : ℝ) * δ = g / 2 := by
          rw [hδdef]; field_simp
        have hgq : g ≤ q.1 j := by
          have := hgle 0
          have h2 : 0 ≤ L 0 * (P 0).1 j := mul_nonneg (hL0 0) ((P 0).2.1 j)
          simp only [hgapdef] at this
          linarith
        set qf : Fin m → ℝ := fun k => q.1 k + δ - if k = j then (m : ℝ) * δ else 0 with hqfdef
        have hqf : qf ∈ stdSimplex ℝ (Fin m) := by
          refine ⟨?_, ?_⟩
          · intro k
            simp only [hqfdef]
            by_cases hk : k = j
            · rw [if_pos hk, hmδ, hk]; linarith
            · rw [if_neg hk]; linarith [q.2.1 k]
          · simp only [hqfdef]
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
            simp [q.2.2]
        refine ⟨⟨qf, hqf⟩, ?_⟩
        have hall : ∀ i, LexGt (P i) qf q.1 := by
          intro i
          unfold LexGt
          apply key _ _ (L i) (sortedR _ _) (minR _ _) (neR _ _)
          intro y hy
          obtain ⟨k, hk, rfl⟩ := (memR _ _ _).mp hy
          by_cases hkj : k = j
          · subst hkj
            rw [lt_div_iff₀ hk]
            simp only [hqfdef, if_true, ite_true, hmδ]
            have := hgle i
            simp only [hgapdef] at this
            linarith
          · simp only [hqfdef, if_neg hkj, sub_zero]
            calc L i ≤ q.1 k / (P i).1 k := leR (P i) q.1 k hk
              _ < (q.1 k + δ) / (P i).1 k := div_lt_div_of_pos_right (by linarith) hk
        exact ⟨fun i => Or.inl (hall i), ⟨0, hall 0⟩⟩
      · intro hc ⟨q', hge, i0, hgt⟩
        by_cases heq : q'.1 = q.1
        · unfold LexGt at hgt
          rw [heq] at hgt
          exact irrL _ hgt
        · have hj : ∃ j, q'.1 j < q.1 j := by
            by_contra hno
            push Not at hno
            apply heq
            have hs : ∑ k, q.1 k = ∑ k, q'.1 k := by rw [q.2.2, q'.2.2]
            have := (Finset.sum_eq_sum_iff_of_le (fun k _ => hno k)).mp hs
            funext k
            exact (this k (Finset.mem_univ k)).symm
          obtain ⟨j, hj⟩ := hj
          have hqj : 0 < q.1 j := lt_of_le_of_lt (q'.2.1 j) hj
          obtain ⟨i, hi⟩ := hc j hqj
          unfold crit at hi
          rw [Finset.mem_filter, Finset.mem_filter] at hi
          obtain ⟨⟨_, hp⟩, hcr⟩ := hi
          have hlex : List.Lex (· < ·) (ratioList (P i) q'.1) (ratioList (P i) q.1) := by
            apply key _ _ (q'.1 j / (P i).1 j) (sortedR _ _) ((memR _ _ _).mpr ⟨j, hp, rfl⟩) (neR _ _)
            intro y hy
            obtain ⟨k, hk, rfl⟩ := (memR _ _ _).mp hy
            calc q'.1 j / (P i).1 j < q.1 j / (P i).1 j := div_lt_div_of_pos_right hj hp
              _ = leontief (P i) q.1 := hcr
              _ ≤ q.1 k / (P i).1 k := leR (P i) q.1 k hk
          rcases hge i with h | h
          · exact asymmL _ _ h hlex
          · unfold LexEq at h
            rw [h] at hlex
            exact irrL _ hlex
