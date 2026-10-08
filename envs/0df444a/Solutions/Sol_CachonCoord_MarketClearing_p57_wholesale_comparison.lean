-- Prove2me | solution 1 for CachonCoord.MarketClearing.p57_wholesale_comparison
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:15:13.788401+00:00
-- url     : https://prove2.me/submissions/b3cd9750-cd17-4c8a-b708-02a7f4cc5920

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model
import Definitions.Def_CachonCoord_MarketClearing_Contracts



namespace CachonCoord.MarketClearing

lemma mc_pl_of_le {q : ℝ} (h : q ≤ 1) : pl q = 1 - q := by
  unfold pl; exact max_eq_left (by linarith)

lemma mc_pl_of_ge {q : ℝ} (h : 1 ≤ q) : pl q = 0 := by
  unfold pl; exact max_eq_right (by linarith)

lemma mc_ph_of_le {θ q : ℝ} (hθ : 0 < θ) (h : q ≤ θ) : ph θ q = 1 - q / θ := by
  unfold ph; apply max_eq_left
  have : q / θ ≤ 1 := (div_le_one hθ).2 h
  linarith

lemma mc_ph_of_ge {θ q : ℝ} (hθ : 0 < θ) (h : θ ≤ q) : ph θ q = 0 := by
  unfold ph; apply max_eq_right
  have : 1 ≤ q / θ := (one_le_div hθ).2 h
  linarith

lemma mc_comp_unique {π : ℝ → ℝ} {q0 : ℝ} (h0 : IsCompetitiveOrder π q0) (q : ℝ) :
    IsCompetitiveOrder π q ↔ q = q0 := by
  constructor
  · rintro ⟨hq, hz, hpos⟩
    rcases lt_trichotomy q q0 with h | h | h
    · have := h0.2.2 q hq h; linarith
    · exact h
    · have := hpos q0 h0.1 h; linarith [h0.2.1]
  · rintro rfl; exact h0

lemma mc_rp_low (θ w x : ℝ) (hθ : 1 < θ) (hx : x ≤ 1) :
    retailerProfit θ w x = x * (1 - w - x * (1 + θ) / (2 * θ)) := by
  unfold retailerProfit
  rw [mc_pl_of_le hx, mc_ph_of_le (by linarith) (by linarith)]
  field_simp; ring

lemma mc_rp_mid (θ w x : ℝ) (hθ : 1 < θ) (hx : 1 ≤ x) (hx2 : x ≤ θ) :
    retailerProfit θ w x = x * ((1 / 2) * (1 - x / θ) - w) := by
  unfold retailerProfit
  rw [mc_pl_of_ge hx, mc_ph_of_le (by linarith) hx2]
  ring

lemma mc_q1_comp (θ w : ℝ) (hθ : 1 < θ) (hw1 : w < 1) (h : wBar0 θ ≤ w) :
    IsCompetitiveOrder (retailerProfit θ w) (q1 θ w) := by
  have hθ0 : 0 < θ := by linarith
  have hq1le : q1 θ w ≤ 1 := by
    unfold q1; unfold wBar0 at h
    rw [div_mul_eq_mul_div, div_le_one (by linarith)]
    have : 1 / (2 * θ) * (2 * θ) = 1 := by field_simp
    nlinarith
  have hq1pos : 0 < q1 θ w := by unfold q1; apply mul_pos (by positivity) (by linarith)
  refine ⟨hq1pos, ?_, ?_⟩
  · rw [mc_rp_low θ w _ hθ hq1le]; unfold q1; field_simp; ring
  · intro x hx hxq
    rw [mc_rp_low θ w _ hθ (by linarith)]
    apply mul_pos hx
    unfold q1 at hxq
    have : x * (1 + θ) < 2 * θ * (1 - w) := by
      have := mul_lt_mul_of_pos_right hxq (show (0:ℝ) < 1 + θ by linarith)
      rw [mul_assoc, div_mul_eq_mul_div] at this
      calc x * (1 + θ) < _ := this
        _ = 2 * θ * (1 - w) := by field_simp
    have : x * (1 + θ) / (2 * θ) < 1 - w := by rw [div_lt_iff₀ (by linarith)]; linarith
    linarith

lemma mc_q2_comp (θ w : ℝ) (hθ : 1 < θ) (hw0 : 0 ≤ w) (h : w < wBar0 θ) :
    IsCompetitiveOrder (retailerProfit θ w) (q2 θ w) := by
  have hθ0 : 0 < θ := by linarith
  unfold wBar0 at h
  have hinv : 1 / (2 * θ) * (2 * θ) = 1 := by field_simp
  have hq2gt : 1 < q2 θ w := by unfold q2; nlinarith
  have hq2le : q2 θ w ≤ θ := by unfold q2; nlinarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [mc_rp_mid θ w _ hθ hq2gt.le hq2le]; unfold q2; field_simp; ring
  · intro x hx hxq
    rcases le_or_gt x 1 with hx1 | hx1
    · rw [mc_rp_low θ w _ hθ hx1]
      apply mul_pos hx
      have e : x * (1 + θ) / (2 * θ) ≤ (1 + θ) / (2 * θ) := by
        apply div_le_div_of_nonneg_right _ (by linarith); nlinarith
      have e2 : (1 + θ) / (2 * θ) = 1 / 2 + 1 / (2 * θ) := by field_simp; ring
      linarith
    · rw [mc_rp_mid θ w _ hθ hx1.le (by linarith)]
      apply mul_pos hx
      unfold q2 at hxq
      have : x / θ < 1 - 2 * w := by rw [div_lt_iff₀ hθ0]; linarith
      linarith

theorem p55_competitive_quantities_core (θ w : ℝ) (hθ : 1 < θ) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    (q1 θ w ≤ 1 ↔ wBar0 θ ≤ w) ∧
    (1 < q2 θ w ↔ w < wBar0 θ) ∧
    (wBar0 θ ≤ w → ∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ w) q ↔ q = q1 θ w) ∧
    (w < wBar0 θ → ∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ w) q ↔ q = q2 θ w) := by
  have hθ0 : 0 < θ := by linarith
  have hinv : 1 / (2 * θ) * (2 * θ) = 1 := by field_simp
  refine ⟨?_, ?_, fun h => mc_comp_unique (mc_q1_comp θ w hθ hw1 h),
    fun h => mc_comp_unique (mc_q2_comp θ w hθ hw0 h)⟩
  · unfold q1 wBar0
    rw [div_mul_eq_mul_div, div_le_one (by linarith)]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · unfold q2 wBar0
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

theorem p57_wholesale_comparison_core (θ : ℝ) (hθ : 1 < θ) :
    (1 + θ) / (4 * θ) < 1 / 2 := by
  rw [div_lt_iff₀ (by linarith)]; linarith

end CachonCoord.MarketClearing

open CachonCoord.MarketClearing


theorem solution (θ : ℝ) (hθ : 1 < θ) :
    (1 + θ) / (4 * θ) < 1 / 2 := by
  exact p57_wholesale_comparison_core θ hθ
