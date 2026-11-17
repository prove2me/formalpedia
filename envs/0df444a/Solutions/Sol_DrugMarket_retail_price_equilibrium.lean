-- Prove2me | solution 1 for DrugMarket.retail_price_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:28:38.751204+00:00
-- url     : https://prove2.me/submissions/d2eed180-c7a8-4d00-a895-2a926cc0b5da

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem retail_price_equilibrium (q t v_r w_a w_b v_a v_b p_a p_b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (ht : 0 < t) (hvr : 0 < v_r) (hva : 0 < v_a) (hvb : 0 < v_b) :
  ((1 - catchRetail q v_r v_a) * ((1:ℝ)/2 - (2*p_a - w_a - p_b)/(2*t)) = 0 ∧ (1 - catchRetail q v_r v_b) * ((1:ℝ)/2 - (2*p_b - w_b - p_a)/(2*t)) = 0) ↔ (p_a = retailPriceA t w_a w_b ∧ p_b = retailPriceB t w_a w_b) := by
  have hc : ∀ v, 0 < v → catchRetail q v_r v < 1 := by
    intro v hv
    unfold catchRetail
    exact Real.rpow_lt_one hq.1.le hq.2 (div_pos hv hvr)
  have ha : 1 - catchRetail q v_r v_a ≠ 0 := by have := hc v_a hva; linarith
  have hb : 1 - catchRetail q v_r v_b ≠ 0 := by have := hc v_b hvb; linarith
  have ht' : (2 * t) ≠ 0 := by positivity
  rw [mul_eq_zero, mul_eq_zero]
  simp only [ha, hb, false_or, retailPriceA, retailPriceB]
  constructor
  · rintro ⟨h1, h2⟩
    rw [sub_eq_zero, eq_div_iff ht'] at h1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    subst h1 h2
    constructor <;> rw [sub_eq_zero, eq_div_iff ht'] <;> ring

end DrugMarket

open DrugMarket in
theorem solution (q t v_r w_a w_b v_a v_b p_a p_b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (ht : 0 < t) (hvr : 0 < v_r) (hva : 0 < v_a) (hvb : 0 < v_b) :
  ((1 - catchRetail q v_r v_a) * ((1:ℝ)/2 - (2*p_a - w_a - p_b)/(2*t)) = 0 ∧ (1 - catchRetail q v_r v_b) * ((1:ℝ)/2 - (2*p_b - w_b - p_a)/(2*t)) = 0) ↔ (p_a = retailPriceA t w_a w_b ∧ p_b = retailPriceB t w_a w_b) := by
  have hc : ∀ v, 0 < v → catchRetail q v_r v < 1 := by
    intro v hv
    unfold catchRetail
    exact Real.rpow_lt_one hq.1.le hq.2 (div_pos hv hvr)
  have ha : 1 - catchRetail q v_r v_a ≠ 0 := by have := hc v_a hva; linarith
  have hb : 1 - catchRetail q v_r v_b ≠ 0 := by have := hc v_b hvb; linarith
  have ht' : (2 * t) ≠ 0 := by positivity
  rw [mul_eq_zero, mul_eq_zero]
  simp only [ha, hb, false_or, retailPriceA, retailPriceB]
  constructor
  · rintro ⟨h1, h2⟩
    rw [sub_eq_zero, eq_div_iff ht'] at h1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    subst h1 h2
    constructor <;> rw [sub_eq_zero, eq_div_iff ht'] <;> ring
