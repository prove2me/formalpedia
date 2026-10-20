-- Prove2me | solution 1 for BrandSpillover.Commitment.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T04:33:10.387514+00:00
-- url     : https://prove2.me/submissions/f234d138-495a-4177-a41a-ef33cec78324

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model
import Theorems.Thm_BrandSpillover_Commitment_lemma_1
import Theorems.Thm_BrandSpillover_Commitment_lemma_2
import Theorems.Thm_BrandSpillover_Commitment_lemma_3
import Theorems.Thm_BrandSpillover_Commitment_committed_game

open BrandSpillover.Commitment SupplierAudit.Competition

theorem solution (P : Params) (hP : P.Standing) (hα : 0 < P.α)
    (s : Structure) (w : ℝ × ℝ) (hs : IsEquilibrium P P.α s w)
    (s₀ : Structure) (w₀ : ℝ × ℝ) (hs₀ : IsEquilibrium P 0 s₀ w₀) :
    (s = .OI → profitW P P.α s w ≤ profitW P 0 s₀ w₀) ∧
    (s ≠ .OI → (profitW P P.α s w < profitW P 0 s₀ w₀ ↔
      P.c < P.θ - 1 / 2 - P.α + P.α * P.θ)) ∧
    (P.c < P.θ - 1 / 2 - P.α + P.α * P.θ ↔
      P.α < (2 * P.θ - 1 - 2 * P.c) / (2 * (1 - P.θ))) := by
  obtain ⟨hc, hθl, h3, ha0, ha1⟩ := id hP
  have h1 : (2 + 7*P.c)/7 ≤ P.θ := le_trans (le_max_left _ _) hθl
  have h2 : (1 + P.c)/2 ≤ P.θ := le_trans (le_max_right _ _) hθl
  -- Firm W's profit at the first-order-condition quantities is the square of its quantity
  have hpW : ∀ (a : ℝ) (s : Structure) (w : ℝ × ℝ), profitW P a s w = (quantW P a s w)^2 := by
    intro a s w; unfold profitW quantS quantW cournotPayoff focQS focQW; ring
  have qW_OI' : ∀ (a : ℝ) (w : ℝ × ℝ), quantW P a .OI w = (2*P.θ - 1 + w.1 - 2*P.c)/3 := by
    intro a w; simp [quantW, focQW, brandW, costS, costW, Structure.sOut, Structure.wOut]
  have qW_OO' : ∀ (a : ℝ) (w : ℝ × ℝ),
      quantW P a .OO w = (2*(P.θ + a*(1-P.θ)) - 1 + w.1 - 2*w.2)/3 := by
    intro a w; simp [quantW, focQW, brandW, costS, costW, Structure.sOut, Structure.wOut]
  -- with commitment: structure (O,O) and the explicit profit
  obtain ⟨-, hc0⟩ := committed_game P hP
  obtain ⟨rfl, hprof0⟩ := hc0 s₀ w₀ hs₀
  rw [hprof0]
  -- without commitment: structure (O,O) or (O,I)
  have hsc := (lemma_1 P hP P.α).2.2 s w hs
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    have e := ((lemma_2 P hP P.α).1 w).1 hs.1
    rw [hpW, qW_OI', e]
    rcases le_total P.c ((2 - P.θ + P.c) / 4) with r | r
    · rw [min_eq_left r]
      split_ifs with h
      · exact le_of_eq (by ring)
      · apply sq_le_sq' <;> linarith
    · rw [min_eq_right r]
      split_ifs with h
      · apply sq_le_sq' <;> linarith
      · apply sq_le_sq' <;> linarith
  · intro hne
    have hOO : s = .OO := hsc.resolve_right hne
    subst hOO
    obtain ⟨e1, e2⟩ := ((lemma_3 P hP P.α ha0 ha1).1 w).1 hs.1
    rw [hpW, qW_OO', e1, e2]
    have hb : 0 < P.α*(1-P.θ) := mul_pos hα (by linarith)
    have hb1 : P.α*(1-P.θ) ≤ 1 - P.θ := by nlinarith
    have hr : P.θ - 1/2 - P.α + P.α*P.θ = P.θ - 1/2 - P.α*(1-P.θ) := by ring
    have hhalf : 1/2*P.α*(1-P.θ) = P.α*(1-P.θ)/2 := by ring
    rw [hr, hhalf]; unfold cOO2
    generalize P.α*(1-P.θ) = b at *
    rcases le_or_gt P.c ((2*P.θ-1-3*b)/2) with r | r
    · rw [min_eq_left (by linarith), if_pos (by linarith), min_eq_left (by linarith),
        if_pos (by linarith)]
      rw [sq_lt_sq₀ (by linarith) (by linarith)]
      constructor <;> intro <;> linarith
    rcases le_or_gt P.c ((1+b)/2) with r2 | r2
    · rw [min_eq_left (by linarith), if_pos r2, min_eq_right (by linarith)]
      split_ifs with h
      · rw [sq_lt_sq₀ (by linarith) (by linarith)]; constructor <;> intro <;> linarith
      · rw [sq_lt_sq₀ (by linarith) (by linarith)]; constructor <;> intro <;> linarith
    · rw [min_eq_right (by linarith), if_neg (by linarith), if_neg (by linarith)]
      rw [sq_lt_sq₀ (by linarith) (by linarith)]; constructor <;> intro <;> linarith
  · rw [lt_div_iff₀ (by linarith)]; constructor <;> intro <;> linarith
