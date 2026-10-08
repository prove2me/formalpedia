-- Prove2me | solution 1 for CachonCoord.MarketClearing.p56_rpm_profit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:21:10.563986+00:00
-- url     : https://prove2.me/submissions/e60af973-9a25-493e-8223-ffaae19717e0

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

lemma mc_wStar_le (θ : ℝ) (hθ : 1 < θ) (h : θ ≤ 3) : wStar θ = 1 / 2 := by
  unfold wStar; simp [h]

lemma mc_wStar_gt (θ : ℝ) (hθ : 1 < θ) (h : 3 < θ) : wStar θ = 1 / 4 := by
  unfold wStar; simp [not_le.2 h]

lemma mc_wBar0_le_half (θ : ℝ) (hθ : 1 < θ) : wBar0 θ ≤ 1 / 2 := by
  unfold wBar0; have : 0 < 1 / (2 * θ) := by positivity
  linarith

lemma mc_quarter_lt_wBar0 (θ : ℝ) (hθ : 3 < θ) : 1 / 4 < wBar0 θ := by
  unfold wBar0
  have : 1 / (2 * θ) < 1 / 6 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

theorem p55_optimal_wholesale_price_core (θ : ℝ) (hθ : 1 < θ) :
    IsMaxOn (supplierProfit θ) (Set.Ico 0 1) (wStar θ) ∧
    supplierProfit θ (wStar θ) = (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) := by
  have hθ0 : 0 < θ := by linarith
  have hval : supplierProfit θ (wStar θ) = (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) := by
    by_cases h : θ ≤ 3
    · rw [mc_wStar_le θ hθ h, if_pos h]
      unfold supplierProfit; rw [if_pos (mc_wBar0_le_half θ hθ)]
      unfold q1; field_simp; ring
    · rw [mc_wStar_gt θ hθ (not_le.1 h), if_neg h]
      unfold supplierProfit; rw [if_neg (not_le.2 (mc_quarter_lt_wBar0 θ (not_le.1 h)))]
      unfold q2; ring
  refine ⟨?_, hval⟩
  intro w hw
  simp only [Set.mem_setOf_eq]
  rw [hval]
  have hA : 2 * θ / (1 + θ) * (1 - w) * w ≤ θ / (2 * (1 + θ)) := by
    have : 2 * θ / (1 + θ) * (1 - w) * w = θ / (2 * (1 + θ)) * (4 * (1 - w) * w) := by
      field_simp; ring
    rw [this]
    have hp : 0 < θ / (2 * (1 + θ)) := by positivity
    nlinarith [sq_nonneg (w - 1 / 2)]
  have hB : θ * (1 - 2 * w) * w ≤ θ / 8 := by nlinarith [sq_nonneg (w - 1 / 4)]
  have hC : θ ≤ 3 → θ / 8 ≤ θ / (2 * (1 + θ)) := by
    intro h; rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  have hD : 3 < θ → θ / (2 * (1 + θ)) ≤ θ / 8 := by
    intro h; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  unfold supplierProfit q1 q2
  split_ifs with h1 h2 h2
  · exact hA
  · linarith [hD (not_le.1 h2)]
  · linarith [hC h2]
  · exact hB

lemma mc_mono_mem (θ : ℝ) (hθ : 1 < θ) : (1 + θ) / 8 ∈ monopolyOutcomes θ := by
  refine ⟨θ / 2, 1 / 2, θ / 2, by norm_num, by linarith, by linarith, le_rfl, ?_⟩
  rw [mc_pl_of_le (by norm_num), mc_ph_of_le (by linarith) (by linarith)]
  field_simp; ring

lemma mc_mono_ub (θ : ℝ) (hθ : 1 < θ) : (1 + θ) / 8 ∈ upperBounds (monopolyOutcomes θ) := by
  rintro v ⟨Q, xl, xh, h1, h2, h3, h4, rfl⟩
  have hθ0 : 0 < θ := by linarith
  have hl : pl xl * xl ≤ 1 / 4 := by
    rcases le_or_gt xl 1 with h | h
    · rw [mc_pl_of_le h]; nlinarith [sq_nonneg (xl - 1 / 2)]
    · rw [mc_pl_of_ge h.le]; norm_num
  have hh : ph θ xh * xh ≤ θ / 4 := by
    rcases le_or_gt xh θ with h | h
    · rw [mc_ph_of_le hθ0 h]
      have : (1 - xh / θ) * xh = (θ * xh - xh ^ 2) / θ := by field_simp
      rw [this, div_le_iff₀ hθ0]; nlinarith [sq_nonneg (xh - θ / 2)]
    · rw [mc_ph_of_ge hθ0 h.le]; linarith
  linarith

theorem p54_monopolist_value_core (θ : ℝ) (hθ : 1 < θ) :
    (1 / 2) * pl (1 / 2) * (1 / 2) + (1 / 2) * ph θ (θ / 2) * (θ / 2) = (1 + θ) / 8 ∧
    (1 / 2 : ℝ) ≤ θ / 2 ∧
    IsGreatest (monopolyOutcomes θ) ((1 + θ) / 8) := by
  refine ⟨?_, by linarith, mc_mono_mem θ hθ, mc_mono_ub θ hθ⟩
  rw [mc_pl_of_le (by norm_num), mc_ph_of_le (by linarith) (by linarith)]
  field_simp; ring

theorem p55_market_prices_core (θ : ℝ) (hθ : 1 < θ) :
    (∃ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q) ∧
    ∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q →
      (θ ≤ 3 → q = q1 θ (wStar θ) ∧ q1 θ (wStar θ) = θ / (1 + θ) ∧
        pl q = 1 / (1 + θ) ∧ ph θ q = θ / (1 + θ)) ∧
      (3 < θ → q = q2 θ (wStar θ) ∧ q2 θ (wStar θ) = θ / 2 ∧
        pl q = 0 ∧ ph θ q = 1 / 2) := by
  have hθ0 : 0 < θ := by linarith
  constructor
  · by_cases h : θ ≤ 3
    · refine ⟨_, mc_q1_comp θ _ hθ ?_ ?_⟩ <;> rw [mc_wStar_le θ hθ h]
      · norm_num
      · exact mc_wBar0_le_half θ hθ
    · refine ⟨_, mc_q2_comp θ _ hθ ?_ ?_⟩ <;> rw [mc_wStar_gt θ hθ (not_le.1 h)]
      · norm_num
      · exact mc_quarter_lt_wBar0 θ (not_le.1 h)
  · intro q hq
    constructor
    · intro h
      have hw := mc_wStar_le θ hθ h
      have hc := mc_q1_comp θ (wStar θ) hθ (by rw [hw]; norm_num) (by rw [hw]; exact mc_wBar0_le_half θ hθ)
      have hqe := (mc_comp_unique hc q).1 hq
      have hq1 : q1 θ (wStar θ) = θ / (1 + θ) := by rw [hw]; unfold q1; field_simp; ring
      have hle : θ / (1 + θ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      refine ⟨hqe, hq1, ?_, ?_⟩
      · rw [hqe, hq1, mc_pl_of_le hle]; field_simp; ring
      · rw [hqe, hq1, mc_ph_of_le hθ0 (by linarith)]; field_simp; ring
    · intro h
      have hw := mc_wStar_gt θ hθ h
      have hc := mc_q2_comp θ (wStar θ) hθ (by rw [hw]; norm_num) (by rw [hw]; exact mc_quarter_lt_wBar0 θ h)
      have hqe := (mc_comp_unique hc q).1 hq
      have hq2 : q2 θ (wStar θ) = θ / 2 := by rw [hw]; unfold q2; ring
      refine ⟨hqe, hq2, ?_, ?_⟩
      · rw [hqe, hq2, mc_pl_of_ge (by linarith)]
      · rw [hqe, hq2, mc_ph_of_le hθ0 (by linarith)]; field_simp; ring

lemma mc_rpm_unit_half (θ : ℝ) (hθ : 1 < θ) :
    rpmUnitRevenue θ (1 / 2) (θ / 2) = 1 / (4 * θ) + 1 / 4 := by
  have hθ0 : 0 < θ := by linarith
  unfold rpmUnitRevenue
  have hpl : ¬ (1 / 2 : ℝ) ≤ pl (θ / 2) := by
    unfold pl; rw [le_max_iff]; push_neg; constructor <;> linarith
  have hph : ph θ (θ / 2) = 1 / 2 := by
    rw [mc_ph_of_le hθ0 (by linarith)]; field_simp; ring
  rw [if_neg hpl, hph, if_pos le_rfl]
  field_simp; ring

theorem p56_rpm_profit_core (θ w y : ℝ) (hθ : 1 < θ) :
    rpmRetailerProfit θ (1 / 2) w (θ / 2) y =
      -y * w + (1 / 2) * (((1 / 2) / (θ / 2)) * y) * (1 / 2) + (1 / 2) * y * (1 / 2) ∧
    rpmRetailerProfit θ (1 / 2) w (θ / 2) y = y * ((1 + θ) / (4 * θ) - w) ∧
    (0 < y → (rpmRetailerProfit θ (1 / 2) w (θ / 2) y = 0 ↔ w = (1 + θ) / (4 * θ))) := by
  have hθ0 : 0 < θ := by linarith
  have e2 : rpmRetailerProfit θ (1 / 2) w (θ / 2) y = y * ((1 + θ) / (4 * θ) - w) := by
    unfold rpmRetailerProfit; rw [mc_rpm_unit_half θ hθ]; field_simp
  refine ⟨?_, e2, ?_⟩
  · rw [e2]; field_simp; ring
  · intro hy; rw [e2]
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · linarith
      · linarith
    · intro h; rw [h]; ring

lemma mc_rpm_unit_mid (θ Q : ℝ) (hθ : 1 < θ) (h1 : 1 / 2 < Q) (h2 : Q ≤ θ / 2) :
    rpmUnitRevenue θ (1 / 2) Q = (1 / 2) * ((1 / 2) * (1 - 1 / 2) / Q) + (1 / 2) * (1 - Q / θ) := by
  have hθ0 : 0 < θ := by linarith
  unfold rpmUnitRevenue
  have hpl : ¬ (1 / 2 : ℝ) ≤ pl Q := by
    unfold pl; rw [le_max_iff]; push_neg; constructor <;> linarith
  have hph : ph θ Q = 1 - Q / θ := mc_ph_of_le hθ0 (by linarith)
  have hph2 : (1 / 2 : ℝ) ≤ 1 - Q / θ := by
    have : Q / θ ≤ 1 / 2 := by rw [div_le_iff₀ hθ0]; linarith
    linarith
  rw [if_neg hpl, hph, if_pos hph2]

lemma mc_rpm_unit_low (θ Q : ℝ) (hθ : 1 < θ) (h1 : Q ≤ 1 / 2) :
    rpmUnitRevenue θ (1 / 2) Q = (1 / 2) * (1 - Q) + (1 / 2) * (1 - Q / θ) := by
  have hθ0 : 0 < θ := by linarith
  unfold rpmUnitRevenue
  have hpl : pl Q = 1 - Q := mc_pl_of_le (by linarith)
  have hph : ph θ Q = 1 - Q / θ := mc_ph_of_le hθ0 (by linarith)
  have hph2 : (1 / 2 : ℝ) ≤ 1 - Q / θ := by
    have : Q / θ ≤ 1 / 2 := by rw [div_le_iff₀ hθ0]; linarith
    linarith
  rw [hpl, hph, if_pos (by linarith), if_pos hph2]

theorem p57_rpm_order_core (θ : ℝ) (hθ : 1 < θ) :
    (∀ w Q y : ℝ, 1 / 2 < Q → Q < θ / 2 →
      rpmRetailerProfit θ (1 / 2) w Q y =
        -y * w + (1 / 2) * (((1 / 2) / Q) * y) * (1 / 2) + (1 / 2) * y * (1 - Q / θ)) ∧
    (∀ w y : ℝ, 0 < y →
      StrictAntiOn (fun Q => rpmRetailerProfit θ (1 / 2) w Q y) (Set.Ioc (1 / 2) (θ / 2))) ∧
    IsCompetitiveOrder (fun Q => rpmRetailerProfit θ (1 / 2) ((1 + θ) / (4 * θ)) Q Q) (θ / 2) ∧
    (1 + θ) / (4 * θ) * (θ / 2) = (1 + θ) / 8 := by
  have hθ0 : 0 < θ := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w Q y h1 h2
    unfold rpmRetailerProfit
    rw [mc_rpm_unit_mid θ Q hθ h1 h2.le]
    have : Q ≠ 0 := by linarith
    field_simp; ring
  · intro w y hy a ha b hb hab
    simp only
    unfold rpmRetailerProfit
    rw [mc_rpm_unit_mid θ a hθ ha.1 ha.2, mc_rpm_unit_mid θ b hθ hb.1 hb.2]
    have ha0 : 0 < a := by linarith [ha.1]
    have h1 : 1 / b < 1 / a := one_div_lt_one_div_of_lt ha0 hab
    have h2 : a / θ < b / θ := div_lt_div_of_pos_right hab hθ0
    have : (1 / 2) * ((1 / 2) * (1 - 1 / 2) / b) + (1 / 2) * (1 - b / θ) <
        (1 / 2) * ((1 / 2) * (1 - 1 / 2) / a) + (1 / 2) * (1 - a / θ) := by
      have e : ∀ c : ℝ, (1 / 2) * ((1 / 2) * (1 - 1 / 2) / c) = (1 / 8) * (1 / c) := by
        intro c; ring
      rw [e, e]; linarith
    nlinarith
  · refine ⟨by linarith, ?_, ?_⟩
    · exact ((p56_rpm_profit_core θ _ _ hθ).2.2 (by linarith)).2 rfl
    · intro x hx hxq
      simp only
      unfold rpmRetailerProfit
      rw [show x * rpmUnitRevenue θ (1 / 2) x - (1 + θ) / (4 * θ) * x =
        x * (rpmUnitRevenue θ (1 / 2) x - (1 + θ) / (4 * θ)) by ring]
      apply mul_pos hx
      apply sub_pos.2
      have hw : (1 + θ) / (4 * θ) = 1 / (4 * θ) + 1 / 4 := by field_simp
      rw [hw]
      rcases le_or_gt x (1 / 2) with h | h
      · rw [mc_rpm_unit_low θ x hθ h]
        have : x / θ ≤ 1 / (2 * θ) := by
          rw [div_le_div_iff₀ hθ0 (by linarith)]; nlinarith
        have e : 1 / (2 * θ) = 2 * (1 / (4 * θ)) := by field_simp; ring
        have : 1 / (4 * θ) < 1 / 4 := by
          rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
        linarith
      · rw [mc_rpm_unit_mid θ x hθ h hxq.le]
        have h1 : 1 / (4 * θ) < (1 / 2) * ((1 / 2) * (1 - 1 / 2) / x) := by
          rw [show (1 / 2 : ℝ) * ((1 / 2) * (1 - 1 / 2) / x) = 1 / (8 * x) by field_simp; ring]
          rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith
        have h2 : x / θ < 1 / 2 := by rw [div_lt_iff₀ hθ0]; linarith
        linarith
  · field_simp; ring

lemma mc_bb_mid (θ w q : ℝ) (hθ : 1 < θ) (h1 : 1 / 2 ≤ q) (h2 : q ≤ θ / 2) :
    bbRetailerProfit θ (1 / 2) w q =
      (1 / 2) * (pl (1 / 2) * (1 / 2) + (1 / 2) * (q - 1 / 2)) + (1 / 2) * (ph θ q * q) - q * w := by
  unfold bbRetailerProfit bbSalesLow bbSalesHigh
  rw [min_eq_right (by linarith), min_eq_left (by linarith)]
  ring

theorem p57_buyback_profit_core (θ : ℝ) (hθ : 1 < θ) :
    (∀ w q : ℝ, 1 / 2 < q → q < θ / 2 →
      bbRetailerProfit θ (1 / 2) w q =
          (1 / 2) * (pl (1 / 2) * (1 / 2) + (1 / 2) * (q - 1 / 2)) + (1 / 2) * (ph θ q * q) - q * w ∧
      bbRetailerProfit θ (1 / 2) w q = q * (3 / 4 - w - q / (2 * θ))) ∧
    bbRetailerProfit θ (1 / 2) (1 / 2) (θ / 2) = 0 := by
  have hθ0 : 0 < θ := by linarith
  refine ⟨fun w q h1 h2 => ⟨mc_bb_mid θ w q hθ h1.le h2.le, ?_⟩, ?_⟩
  · rw [mc_bb_mid θ w q hθ h1.le h2.le, mc_pl_of_le (by norm_num), mc_ph_of_le hθ0 (by linarith)]
    field_simp; ring
  · rw [mc_bb_mid θ _ _ hθ (by linarith) le_rfl, mc_pl_of_le (by norm_num),
      mc_ph_of_le hθ0 (by linarith)]
    field_simp; ring

lemma mc_bb_comp (θ : ℝ) (hθ : 1 < θ) :
    IsCompetitiveOrder (bbRetailerProfit θ (1 / 2) (1 / 2)) (θ / 2) := by
  have hθ0 : 0 < θ := by linarith
  refine ⟨by linarith, (p57_buyback_profit_core θ hθ).2, ?_⟩
  intro x hx hxq
  rcases le_or_gt x (1 / 2) with h | h
  · have e : bbRetailerProfit θ (1 / 2) (1 / 2) x = (x / 2) * (1 - x - x / θ) := by
      unfold bbRetailerProfit bbSalesLow bbSalesHigh
      rw [min_eq_left (show x ≤ 1 - 1 / 2 by linarith), min_eq_left (show x ≤ θ * (1 - 1 / 2) by linarith), mc_pl_of_le (by linarith),
        mc_ph_of_le hθ0 (by linarith)]
      ring
    rw [e]
    apply mul_pos (by linarith)
    have : x / θ ≤ 1 / (2 * θ) := by
      rw [div_le_div_iff₀ hθ0 (by linarith)]; nlinarith
    have : 1 / (2 * θ) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  · rw [((p57_buyback_profit_core θ hθ).1 _ x h hxq).2]
    apply mul_pos hx
    have : x / (2 * θ) < 1 / 4 := by rw [div_lt_iff₀ (by linarith)]; linarith
    linarith

lemma mc_rp_neg (θ w x : ℝ) (hθ : 1 < θ) (hw : 1 ≤ w) (hx : 0 < x) :
    retailerProfit θ w x < 0 := by
  have hθ0 : 0 < θ := by linarith
  unfold retailerProfit
  have h1 : pl x < 1 := by unfold pl; rw [max_lt_iff]; constructor <;> linarith
  have h2 : ph θ x < 1 := by
    unfold ph; rw [max_lt_iff]; constructor
    · have : 0 < x / θ := by positivity
      linarith
    · norm_num
  nlinarith

theorem sec_6_5_2_core (θ : ℝ) (hθ : 1 < θ) :
    IsGreatest (wholesaleOutcomes θ) (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) ∧
    (∃ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q) ∧
    (∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q →
      wStar θ * q = (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8)) ∧
    IsGreatest (monopolyOutcomes θ) ((1 + θ) / 8) ∧
    (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) < (1 + θ) / 8 ∧
    IsCompetitiveOrder (bbRetailerProfit θ (1 / 2) (1 / 2)) (θ / 2) ∧
    bbSupplierProfit θ (1 / 2) (1 / 2) (θ / 2) = (1 + θ) / 8 := by
  have hθ0 : 0 < θ := by linarith
  obtain ⟨hmax, hval⟩ := p55_optimal_wholesale_price_core θ hθ
  -- competitive orders at w in [0,1) give w*q = supplierProfit
  have key : ∀ w q, 0 ≤ w → w < 1 → IsCompetitiveOrder (retailerProfit θ w) q →
      w * q = supplierProfit θ w := by
    intro w q hw0 hw1 hq
    obtain ⟨-, -, h3, h4⟩ := p55_competitive_quantities_core θ w hθ hw0 hw1
    unfold supplierProfit
    split_ifs with h
    · rw [(h3 h q).1 hq]; ring
    · rw [(h4 (not_le.1 h) q).1 hq]; ring
  have hws0 : 0 ≤ wStar θ := by unfold wStar; split_ifs <;> norm_num
  have hws1 : wStar θ < 1 := by unfold wStar; split_ifs <;> norm_num
  obtain ⟨⟨q0, hq0⟩, -⟩ := p55_market_prices_core θ hθ
  have hvpos : 0 ≤ (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) := by
    split_ifs <;> positivity
  refine ⟨⟨⟨wStar θ, q0, hq0, ?_⟩, ?_⟩, ⟨q0, hq0⟩, ?_, ?_, ?_, mc_bb_comp θ hθ, ?_⟩
  · rw [key _ _ hws0 hws1 hq0, hval]
  · rintro v ⟨w, q, hq, rfl⟩
    rcases lt_or_ge w 0 with hw | hw
    · have := hq.1; nlinarith
    rcases lt_or_ge w 1 with hw1 | hw1
    · rw [key w q hw hw1 hq, ← hval]; exact hmax ⟨hw, hw1⟩
    · have := mc_rp_neg θ w q hθ hw1 hq.1; linarith [hq.2.1]
  · intro q hq; rw [key _ _ hws0 hws1 hq, hval]
  · exact (p54_monopolist_value_core θ hθ).2.2
  · split_ifs with h
    · rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    · rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]; linarith
  · unfold bbSupplierProfit bbSalesLow bbSalesHigh
    rw [min_eq_right (by linarith), min_eq_left (by linarith)]
    ring

end CachonCoord.MarketClearing

open CachonCoord.MarketClearing


theorem solution (θ w y : ℝ) (hθ : 1 < θ) :
    rpmRetailerProfit θ (1 / 2) w (θ / 2) y =
      -y * w + (1 / 2) * (((1 / 2) / (θ / 2)) * y) * (1 / 2) + (1 / 2) * y * (1 / 2) ∧
    rpmRetailerProfit θ (1 / 2) w (θ / 2) y = y * ((1 + θ) / (4 * θ) - w) ∧
    (0 < y → (rpmRetailerProfit θ (1 / 2) w (θ / 2) y = 0 ↔ w = (1 + θ) / (4 * θ))) := by
  exact p56_rpm_profit_core θ w y hθ
