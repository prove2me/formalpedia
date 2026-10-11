-- Prove2me | solution 1 for ComparativeAdvantage.terms_of_trade_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:50:20.13404+00:00
-- url     : https://prove2.me/submissions/3a5efb6c-1b56-4ab1-ba98-937b3651519d

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ComparativeAdvantage

theorem solution (c : Country) (PC PW : ℝ) (hPC : 0 < PC) (hPW : 0 < PW) :
    (autarkySet c ⊆ tradeSetCloth c PC PW ↔ c.aLC / c.aLW ≤ PC / PW) ∧
    (autarkySet c ⊆ tradeSetWine c PC PW ↔ PC / PW ≤ c.aLC / c.aLW) := by
  have hLC : c.aLC ≠ 0 := ne_of_gt c.aLC_pos
  have hLW : c.aLW ≠ 0 := ne_of_gt c.aLW_pos
  have hcloth_eq : c.aLC * (PW / PC) = (c.aLC * PW) / PC := by ring
  have hwine_eq : c.aLW * (PC / PW) = (c.aLW * PC) / PW := by ring
  constructor
  · constructor
    · intro hs
      have hq : ((0 : ℝ), c.L / c.aLW) ∈ autarkySet c := by
        have heq : c.aLW * (c.L / c.aLW) = c.L := by
          field_simp [hLW]
        refine ⟨by norm_num, le_of_lt (div_pos c.L_pos c.aLW_pos), ?_⟩
        dsimp
        nlinarith
      rcases hs hq with ⟨_, _, htrade⟩
      have hcoef : c.aLC * (PW / PC) ≤ c.aLW := by
        by_contra hc
        have hlt : c.aLW < c.aLC * (PW / PC) := lt_of_not_ge hc
        have hm := mul_lt_mul_of_pos_right hlt
          (div_pos c.L_pos c.aLW_pos)
        have heq : c.aLW * (c.L / c.aLW) = c.L := by
          field_simp [hLW]
        dsimp at htrade
        nlinarith
      rw [hcloth_eq] at hcoef
      have hcross := (div_le_iff₀ hPC).1 hcoef
      exact (div_le_div_iff₀ c.aLW_pos hPW).2 (by nlinarith)
    · intro hp q hq
      rcases hq with ⟨hx, hy, hbudget⟩
      have hcross := (div_le_div_iff₀ c.aLW_pos hPW).1 hp
      have hcoef : c.aLC * (PW / PC) ≤ c.aLW := by
        rw [hcloth_eq]
        exact (div_le_iff₀ hPC).2 (by nlinarith)
      have hm := mul_le_mul_of_nonneg_right hcoef hy
      exact ⟨hx, hy, by nlinarith⟩
  · constructor
    · intro hs
      have hq : ((c.L / c.aLC), (0 : ℝ)) ∈ autarkySet c := by
        have heq : c.aLC * (c.L / c.aLC) = c.L := by
          field_simp [hLC]
        refine ⟨le_of_lt (div_pos c.L_pos c.aLC_pos), by norm_num, ?_⟩
        dsimp
        nlinarith
      rcases hs hq with ⟨_, _, htrade⟩
      have hcoef : c.aLW * (PC / PW) ≤ c.aLC := by
        by_contra hc
        have hlt : c.aLC < c.aLW * (PC / PW) := lt_of_not_ge hc
        have hm := mul_lt_mul_of_pos_right hlt
          (div_pos c.L_pos c.aLC_pos)
        have heq : c.aLC * (c.L / c.aLC) = c.L := by
          field_simp [hLC]
        dsimp at htrade
        nlinarith
      rw [hwine_eq] at hcoef
      have hcross := (div_le_iff₀ hPW).1 hcoef
      exact (div_le_div_iff₀ hPW c.aLW_pos).2 (by nlinarith)
    · intro hp q hq
      rcases hq with ⟨hx, hy, hbudget⟩
      have hcross := (div_le_div_iff₀ hPW c.aLW_pos).1 hp
      have hcoef : c.aLW * (PC / PW) ≤ c.aLC := by
        rw [hwine_eq]
        exact (div_le_iff₀ hPW).2 (by nlinarith)
      have hm := mul_le_mul_of_nonneg_right hcoef hx
      exact ⟨hx, hy, by nlinarith⟩
