-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:51.89553+00:00
-- url     : https://prove2.me/submissions/de39faa9-8102-4021-9d76-b7f810a3bf32

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Lemma 15, p. 40: if `q″ ⪰lex_p q′` then every alternative critical at `q′` for
the peak `p` receives at least as much in `q″` as in `q′`. -/
theorem solution {m : ℕ} (p q₁ q₂ : stdSimplex ℝ (Fin m))
    (h : LexGe p q₂.1 q₁.1) :
    ∀ y ∈ crit p q₁.1, q₁.1 y ≤ q₂.1 y := by
      classical
      intro y hy
      have hyp : 0 < p.1 y := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
      have hycrit : q₁.1 y / p.1 y = leontief p q₁.1 := (Finset.mem_filter.mp hy).2
      have hlower : ∀ x ∈ ratioList p q₁.1, leontief p q₁.1 ≤ x := by
        intro x hx
        simp only [ratioList, Multiset.mem_sort, Multiset.mem_map] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        exact Finset.inf'_le _ (by simpa using hj)
      have hmem₁ : q₁.1 y / p.1 y ∈ ratioList p q₁.1 := by
        simp only [ratioList, Multiset.mem_sort, Multiset.mem_map]
        exact ⟨y, by simpa using hyp, rfl⟩
      have hmem₂ : q₂.1 y / p.1 y ∈ ratioList p q₂.1 := by
        simp only [ratioList, Multiset.mem_sort, Multiset.mem_map]
        exact ⟨y, by simpa using hyp, rfl⟩
      have hsorted₂ : (ratioList p q₂.1).Pairwise (· ≤ ·) := by
        exact Multiset.pairwise_sort _ _
      have hratio : leontief p q₁.1 ≤ q₂.1 y / p.1 y := by
        rcases h with h | h
        · change List.Lex (· < ·) (ratioList p q₁.1) (ratioList p q₂.1) at h
          cases he₁ : ratioList p q₁.1 with
          | nil => simp [he₁] at hmem₁
          | cons a as =>
            cases he₂ : ratioList p q₂.1 with
            | nil => simp [he₂] at hmem₂
            | cons b bs =>
              rw [he₁, he₂] at h
              have hab : a ≤ b := by
                cases h with
                | rel hab => exact hab.le
                | cons _ => exact le_rfl
              have hla : leontief p q₁.1 ≤ a := hlower a (by simp [he₁])
              have hby : b ≤ q₂.1 y / p.1 y := by
                rw [he₂] at hsorted₂ hmem₂
                rcases List.mem_cons.mp hmem₂ with heq | htail
                · exact le_of_eq heq.symm
                · exact (List.pairwise_cons.mp hsorted₂).1 _ htail
              exact hla.trans (hab.trans hby)
        · change ratioList p q₂.1 = ratioList p q₁.1 at h
          exact hlower _ (h ▸ hmem₂)
      exact (div_le_div_iff_of_pos_right hyp).mp (hycrit ▸ hratio)
