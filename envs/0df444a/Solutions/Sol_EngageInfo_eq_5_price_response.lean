-- Prove2me | solution 1 for EngageInfo.eq_5_price_response
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:24:09.1045+00:00
-- url     : https://prove2.me/submissions/a749bcf4-d29d-442f-bbdb-857dd6992acb

import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_subgame

namespace Aux_EngageInfo_eq_5
open EngageInfo

lemma effort_nonneg (M : Params) (b : Bool) : 0 ≤ effort M b := by
  cases b
  · simp [effort]
  · simp only [effort, ↓reduceIte]
    linarith [M.k_pos, M.k_lt_ebar]

lemma low_margin_pos (M : Params) (b : Bool) : 0 < M.θL + effort M b - M.c := by
  linarith [M.c_lt_θL, effort_nonneg M b]

lemma high_margin_pos (M : Params) (b : Bool) : 0 < M.θH + effort M b - M.c := by
  linarith [M.c_lt_θL, M.θL_lt_θH, effort_nonneg M b]

lemma profit_at_low (M : Params) (α e : ℝ) (h : M.θL < M.θH) :
    sellerProfit M α e (M.θL + e) = M.θL + e - M.c := by
  have hle : M.θL + e ≤ M.θH + e := by linarith
  simp [sellerProfit, hle]

lemma profit_at_high (M : Params) (α e : ℝ) (h : M.θL < M.θH) :
    sellerProfit M α e (M.θH + e) = α * (M.θH + e - M.c) := by
  have hnle : ¬ (M.θH + e ≤ M.θL + e) := by linarith
  simp [sellerProfit, hnle]
  ring

lemma profit_le_max (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (b : Bool) (p : ℝ) :
    sellerProfit M α (effort M b) p ≤
      max (M.θL + effort M b - M.c) (α * (M.θH + effort M b - M.c)) := by
  set e := effort M b
  rcases hα with ⟨hα0, hα1⟩
  have hlow_pos : 0 < M.θL + e - M.c := low_margin_pos M b
  by_cases hpL : p ≤ M.θL + e
  · have hpH : p ≤ M.θH + e := by linarith [M.θL_lt_θH]
    have hval : sellerProfit M α e p = p - M.c := by
      simp [sellerProfit, hpL, hpH]
    rw [hval]
    exact le_trans (by linarith) (le_max_left _ _)
  · push_neg at hpL
    by_cases hpH : p ≤ M.θH + e
    · have hnL : ¬ (p ≤ M.θL + e) := not_le.mpr hpL
      have hval : sellerProfit M α e p = α * (p - M.c) := by
        simp [sellerProfit, hnL, hpH]; ring
      rw [hval]
      refine le_trans ?_ (le_max_right _ _)
      exact mul_le_mul_of_nonneg_left (by linarith) hα0
    · have hnL : ¬ (p ≤ M.θL + e) := not_le.mpr hpL
      have hval : sellerProfit M α e p = 0 := by
        simp [sellerProfit, hnL, hpH]
      rw [hval]
      exact le_trans hlow_pos.le (le_max_left _ _)

lemma profit_eq_max_iff (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (b : Bool) (p : ℝ) :
    sellerProfit M α (effort M b) p =
      max (M.θL + effort M b - M.c) (α * (M.θH + effort M b - M.c)) ↔
      ((α < M.alpha (effort M b) ∧ p = M.θL + effort M b) ∨
        (M.alpha (effort M b) < α ∧ p = M.θH + effort M b) ∨
        (α = M.alpha (effort M b) ∧ (p = M.θL + effort M b ∨ p = M.θH + effort M b))) := by
  set e := effort M b
  rcases hα with ⟨hα0, hα1⟩
  have hLpos : 0 < M.θL + e - M.c := low_margin_pos M b
  have hHpos : 0 < M.θH + e - M.c := high_margin_pos M b
  have hlt_iff : α < M.alpha e ↔ α * (M.θH + e - M.c) < M.θL + e - M.c := by
    unfold Params.alpha
    exact lt_div_iff₀ hHpos
  have hgt_iff : M.alpha e < α ↔ M.θL + e - M.c < α * (M.θH + e - M.c) := by
    unfold Params.alpha
    exact div_lt_iff₀ hHpos
  have heq_iff : α = M.alpha e ↔ α * (M.θH + e - M.c) = M.θL + e - M.c := by
    unfold Params.alpha
    exact eq_div_iff hHpos.ne'
  constructor
  · intro heq
    have hBpos : 0 < max (M.θL + e - M.c) (α * (M.θH + e - M.c)) :=
      lt_of_lt_of_le hLpos (le_max_left _ _)
    by_cases hpL : p ≤ M.θL + e
    · have hpH : p ≤ M.θH + e := by linarith [M.θL_lt_θH]
      have hval : sellerProfit M α e p = p - M.c := by simp [sellerProfit, hpL, hpH]
      rw [hval] at heq
      have hge : max (M.θL + e - M.c) (α * (M.θH + e - M.c)) ≤ M.θL + e - M.c := by linarith
      have hHleL : α * (M.θH + e - M.c) ≤ M.θL + e - M.c :=
        le_trans (le_max_right _ _) hge
      have hp_eq : p = M.θL + e := by
        have := le_max_left (M.θL + e - M.c) (α * (M.θH + e - M.c))
        linarith
      rcases lt_or_eq_of_le hHleL with hlt | hsame
      · exact Or.inl ⟨hlt_iff.mpr hlt, hp_eq⟩
      · exact Or.inr (Or.inr ⟨heq_iff.mpr hsame, Or.inl hp_eq⟩)
    · push_neg at hpL
      by_cases hpH : p ≤ M.θH + e
      · have hnL : ¬ (p ≤ M.θL + e) := not_le.mpr hpL
        have hval : sellerProfit M α e p = α * (p - M.c) := by simp [sellerProfit, hnL, hpH]; ring
        rw [hval] at heq
        have hαpos : 0 < α := by
          rcases eq_or_lt_of_le hα0 with rfl | hpos
          · simp at heq; linarith
          · exact hpos
        have hleH : α * (p - M.c) ≤ α * (M.θH + e - M.c) :=
          mul_le_mul_of_nonneg_left (by linarith) hα0
        have hB_le : max (M.θL + e - M.c) (α * (M.θH + e - M.c)) ≤ α * (M.θH + e - M.c) := by
          linarith
        have hLleH : M.θL + e - M.c ≤ α * (M.θH + e - M.c) :=
          le_trans (le_max_left _ _) hB_le
        have hp_eq : p = M.θH + e := by
          have h1 : α * (M.θH + e - M.c) ≤ α * (p - M.c) := by
            have := le_max_right (M.θL + e - M.c) (α * (M.θH + e - M.c))
            linarith
          have h2 : M.θH + e - M.c ≤ p - M.c := le_of_mul_le_mul_left h1 hαpos
          linarith
        rcases lt_or_eq_of_le hLleH with hgt | hsame
        · exact Or.inr (Or.inl ⟨hgt_iff.mpr hgt, hp_eq⟩)
        · exact Or.inr (Or.inr ⟨heq_iff.mpr hsame.symm, Or.inr hp_eq⟩)
      · have hnL : ¬ (p ≤ M.θL + e) := not_le.mpr hpL
        have hval : sellerProfit M α e p = 0 := by simp [sellerProfit, hnL, hpH]
        rw [hval] at heq
        linarith
  · rintro (⟨hlt, rfl⟩ | ⟨hgt, rfl⟩ | ⟨hsame, rfl | rfl⟩)
    · rw [profit_at_low M α e M.θL_lt_θH]
      exact (max_eq_left (hlt_iff.mp hlt).le).symm
    · rw [profit_at_high M α e M.θL_lt_θH]
      exact (max_eq_right (hgt_iff.mp hgt).le).symm
    · rw [profit_at_low M α e M.θL_lt_θH]
      exact (max_eq_left (heq_iff.mp hsame).le).symm
    · rw [profit_at_high M α e M.θL_lt_θH]
      exact (max_eq_right (heq_iff.mp hsame).ge).symm

end Aux_EngageInfo_eq_5

open EngageInfo Aux_EngageInfo_eq_5

theorem solution (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (b : Bool) :
    (∀ p : ℝ, (∀ p' : ℝ, sellerProfit M α (effort M b) p' ≤ sellerProfit M α (effort M b) p) ↔
      ((α < M.alpha (effort M b) ∧ p = M.θL + effort M b) ∨
        (M.alpha (effort M b) < α ∧ p = M.θH + effort M b) ∨
        (α = M.alpha (effort M b) ∧ (p = M.θL + effort M b ∨ p = M.θH + effort M b)))) ∧
    IsGreatest (Set.range (sellerProfit M α (effort M b)))
      (max (M.θL + effort M b - M.c) (α * (M.θH + effort M b - M.c))) := by
  set e := effort M b
  set B := max (M.θL + e - M.c) (α * (M.θH + e - M.c))
  have hmem : B ∈ Set.range (sellerProfit M α e) := by
    rcases le_total (α * (M.θH + e - M.c)) (M.θL + e - M.c) with hle | hge
    · refine ⟨M.θL + e, ?_⟩
      rw [profit_at_low M α e M.θL_lt_θH]
      exact (max_eq_left hle).symm
    · refine ⟨M.θH + e, ?_⟩
      rw [profit_at_high M α e M.θL_lt_θH]
      exact (max_eq_right hge).symm
  have hgreat : IsGreatest (Set.range (sellerProfit M α e)) B := by
    refine ⟨hmem, ?_⟩
    rintro _ ⟨p', rfl⟩
    exact profit_le_max M α hα b p'
  refine ⟨fun p => ?_, hgreat⟩
  rw [← profit_eq_max_iff M α hα b p]
  rcases hmem with ⟨pStar, hpStar⟩
  constructor
  · intro hp
    refine le_antisymm (profit_le_max M α hα b p) ?_
    calc B = sellerProfit M α e pStar := hpStar.symm
      _ ≤ sellerProfit M α e p := hp pStar
  · intro hp p'
    rw [hp]
    exact profit_le_max M α hα b p'
