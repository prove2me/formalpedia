-- Prove2me | solution 1 for ChannelRebate.Quantity.theorem1_target_rebate_coordination
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:25:46.616652+00:00
-- url     : https://prove2.me/submissions/6f0d4a13-ce73-41fa-8767-a970add9ea78

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts
import Definitions.Def_ChannelRebate_Quantity_Setting
open MeasureTheory

namespace ChannelRebate.Quantity.Thm1Aux

open CachonCoord.Newsvendor

lemma phi_nonneg (D : Demand) (x : ℝ) : 0 ≤ D.φ x := by
  rcases lt_or_ge x 0 with h | h
  · rw [D.φ_eq_zero_of_neg x h]
  · exact (D.φ_pos x h).le

lemma integral_law (D : Demand) (g : ℝ → ℝ) :
    ∫ x, g x ∂D.law = ∫ x, D.φ x * g x := by
  unfold Demand.law
  have : (fun x => ENNReal.ofReal (D.φ x)) =
      fun x => ((Real.toNNReal (D.φ x) : NNReal) : ENNReal) := rfl
  rw [this, integral_withDensity_eq_integral_smul D.measurable_φ.real_toNNReal]
  congr 1
  ext x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (phi_nonneg D x), smul_eq_mul]

lemma int_phi_mul_min (D : Demand) (Q : ℝ) : Integrable (fun x => D.φ x * min Q x) := by
  refine Integrable.mono' ((D.integrable_φ.const_mul |Q|).add D.integrable_mul_φ.abs)
    (D.measurable_φ.mul (measurable_const.min measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have h0 := phi_nonneg D x
  have h1 : |min Q x| ≤ |Q| + |x| :=
    (abs_min_le_max_abs_abs).trans (max_le (by linarith [abs_nonneg x]) (by linarith [abs_nonneg Q]))
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h1 h0]

lemma ii_phi (D : Demand) (a b : ℝ) : IntervalIntegrable D.φ volume a b :=
  D.integrable_φ.intervalIntegrable

lemma ii_xphi (D : Demand) (a b : ℝ) : IntervalIntegrable (fun x => x * D.φ x) volume a b :=
  D.integrable_mul_φ.intervalIntegrable

lemma phi_cont (D : Demand) : Continuous (Phi D) :=
  intervalIntegral.continuous_primitive (fun a b => ii_phi D a b) 0

lemma gam_cont (D : Demand) : Continuous (Gam D) :=
  intervalIntegral.continuous_primitive (fun a b => ii_xphi D a b) 0

lemma phi_zero (D : Demand) : Phi D 0 = 0 := by simp [Phi]

lemma gam_zero (D : Demand) : Gam D 0 = 0 := by simp [Gam]

lemma phi_sub (D : Demand) (a b : ℝ) : Phi D b - Phi D a = ∫ x in a..b, D.φ x := by
  unfold Phi
  exact intervalIntegral.integral_interval_sub_left (ii_phi D _ _) (ii_phi D _ _)

lemma gam_sub (D : Demand) (a b : ℝ) : Gam D b - Gam D a = ∫ x in a..b, x * D.φ x := by
  unfold Gam
  exact intervalIntegral.integral_interval_sub_left (ii_xphi D _ _) (ii_xphi D _ _)

lemma phi_strict (D : Demand) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : Phi D a < Phi D b := by
  have : 0 < ∫ x in a..b, D.φ x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (ii_phi D a b)
      (fun x hx => D.φ_pos x (by linarith [hx.1])) hab
  linarith [phi_sub D a b]

lemma gam_strict (D : Demand) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : Gam D a < Gam D b := by
  have : 0 < ∫ x in a..b, x * D.φ x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (ii_xphi D a b)
      (fun x hx => mul_pos (by linarith [hx.1]) (D.φ_pos x (by linarith [hx.1]))) hab
  linarith [gam_sub D a b]

lemma phi_le_one (D : Demand) (b : ℝ) (hb : 0 ≤ b) : Phi D b ≤ 1 := by
  unfold Phi
  rw [intervalIntegral.integral_of_le hb, ← D.integral_φ]
  exact setIntegral_le_integral D.integrable_φ (Filter.Eventually.of_forall (phi_nonneg D))

/-- The key inequality: `a (Φ b − Φ a) < Γ b − Γ a` for distinct `a, b ≥ 0`. -/
lemma key (D : Demand) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b) :
    a * (Phi D b - Phi D a) < Gam D b - Gam D a := by
  rcases lt_or_gt_of_ne hab with h | h
  · have hpos : 0 < ∫ x in a..b, (x - a) * D.φ x :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        (((ii_xphi D a b).sub ((ii_phi D a b).const_mul a)).congr (fun x _ => by ring))
        (fun x hx => mul_pos (by linarith [hx.1]) (D.φ_pos x (by linarith [hx.1]))) h
    have e : ∫ x in a..b, (x - a) * D.φ x = (Gam D b - Gam D a) - a * (Phi D b - Phi D a) := by
      rw [gam_sub, phi_sub, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (ii_xphi D a b) ((ii_phi D a b).const_mul a)]
      congr 1; ext x; ring
    linarith
  · have hpos : 0 < ∫ x in b..a, (a - x) * D.φ x :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        ((((ii_phi D b a).const_mul a).sub (ii_xphi D b a)).congr (fun x _ => by ring))
        (fun x hx => mul_pos (by linarith [hx.2]) (D.φ_pos x (by linarith [hx.1]))) h
    have e : ∫ x in b..a, (a - x) * D.φ x = a * (Phi D a - Phi D b) - (Gam D a - Gam D b) := by
      rw [gam_sub, phi_sub, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub ((ii_phi D b a).const_mul a) (ii_xphi D b a)]
      congr 1; ext x; ring
    linarith

/-- Expected sales `S(T) = Γ(T) + T(1 − Φ(T))`. -/
noncomputable def S (D : Demand) (T : ℝ) : ℝ := Gam D T + T * (1 - Phi D T)

lemma S_strict (D : Demand) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : S D a < S D b := by
  have hk := key D a b ha (by linarith) hab.ne
  have h1 := phi_le_one D b (by linarith)
  unfold S
  nlinarith

lemma leftover_aux (D : Demand) (Q : ℝ) :
    ∫ x, D.φ x * max (Q - x) 0 = Q - ∫ x, D.φ x * min Q x := by
  have : (fun x => D.φ x * max (Q - x) 0) = fun x => Q * D.φ x - D.φ x * min Q x := by
    ext x
    rcases le_total Q x with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [this, integral_sub (D.integrable_φ.const_mul Q) (int_phi_mul_min D Q), integral_const_mul,
    D.integral_φ]
  ring

lemma leftover_eq (D : Demand) (Q : ℝ) (hQ : 0 ≤ Q) :
    expLeftover D.law Q = Q * Phi D Q - Gam D Q := by
  unfold expLeftover
  rw [integral_law]
  have : (fun x => D.φ x * max (Q - x) 0) =
      Set.indicator (Set.Icc 0 Q) (fun x => (Q - x) * D.φ x) := by
    ext x
    by_cases hx : x ∈ Set.Icc 0 Q
    · rw [Set.indicator_of_mem hx, max_eq_left (by linarith [hx.2])]; ring
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · rw [D.φ_eq_zero_of_neg x hx]; simp
      · rw [max_eq_right (by linarith)]; simp
  rw [this, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hQ]
  unfold Phi Gam
  have e : (fun x => (Q - x) * D.φ x) = fun x => Q * D.φ x - x * D.φ x := by ext; ring
  rw [e, intervalIntegral.integral_sub ((ii_phi D 0 Q).const_mul Q) (ii_xphi D 0 Q),
    intervalIntegral.integral_const_mul]

lemma sales_eq (D : Demand) (Q : ℝ) (hQ : 0 ≤ Q) : expSales D.law Q = S D Q := by
  have h1 := leftover_eq D Q hQ
  unfold expLeftover at h1
  rw [integral_law, leftover_aux] at h1
  unfold expSales S
  rw [integral_law]
  linarith

lemma rebate_le (D : Demand) (Q T : ℝ) (h : Q ≤ T) : rebateUnits D Q T = 0 := by
  unfold rebateUnits
  have : (fun x => max (min Q x - T) 0) = fun _ => (0 : ℝ) := by
    ext x; exact max_eq_right (by linarith [min_le_left Q x])
  rw [this, integral_zero]

lemma rebate_gt (D : Demand) (Q T : ℝ) (hT : 0 ≤ T) (h : T ≤ Q) :
    rebateUnits D Q T = S D Q - S D T := by
  rw [← sales_eq D Q (by linarith), ← sales_eq D T hT]
  unfold rebateUnits expSales
  rw [integral_law, integral_law, integral_law,
    ← integral_sub (int_phi_mul_min D Q) (int_phi_mul_min D T)]
  congr 1; ext x
  rw [← mul_sub]
  congr 1
  rcases le_total x T with h1 | h1
  · rw [min_eq_right (by linarith), min_eq_right h1, max_eq_right (by linarith)]; ring
  · rcases le_total x Q with h2 | h2
    · rw [min_eq_right h2, min_eq_left h1, max_eq_left (by linarith)]
    · rw [min_eq_left h2, min_eq_left h1, max_eq_left (by linarith)]

/-- Newsvendor profit in closed form. -/
noncomputable def F (D : Demand) (s a w Q : ℝ) : ℝ :=
  (a - s) * Gam D Q + Q * ((a - w) - (a - s) * Phi D Q)

lemma base_eq (D : Demand) (p s w Q : ℝ) (hQ : 0 ≤ Q) :
    -w * Q + p * expSales D.law Q + s * expLeftover D.law Q = F D s p w Q := by
  rw [sales_eq D Q hQ, leftover_eq D Q hQ]
  unfold S F; ring

lemma wholesale_eq (D : Demand) (p s w Q : ℝ) (hQ : 0 ≤ Q) :
    wholesaleProfit p s w D Q = F D s p w Q := base_eq D p s w Q hQ

lemma retailer_le (D : Demand) (p s w u T Q : ℝ) (hQ : 0 ≤ Q) (h : Q ≤ T) :
    retailerProfit p s w u T D Q = F D s p w Q := by
  unfold retailerProfit
  rw [base_eq D p s w Q hQ, rebate_le D Q T h]; ring

lemma retailer_gt (D : Demand) (p s w u T Q : ℝ) (hT : 0 ≤ T) (h : T < Q) :
    retailerProfit p s w u T D Q = F D s (p + u) w Q - u * S D T := by
  unfold retailerProfit
  rw [base_eq D p s w Q (by linarith), rebate_gt D Q T hT h.le]
  unfold F S; ring

lemma F_crit (D : Demand) (s a w Q : ℝ) (h : (a - w) - (a - s) * Phi D Q = 0) :
    F D s a w Q = (a - s) * Gam D Q := by
  unfold F; rw [h]; ring

lemma F_lt (D : Demand) (s a w Qs Q : ℝ) (has : s < a) (hQs : 0 ≤ Qs) (hQ : 0 ≤ Q)
    (hne : Q ≠ Qs) (h : (a - w) - (a - s) * Phi D Qs = 0) :
    F D s a w Q < F D s a w Qs := by
  have hk := key D Q Qs hQ hQs hne
  have : F D s a w Qs - F D s a w Q =
      (a - s) * ((Gam D Qs - Gam D Q) - Q * (Phi D Qs - Phi D Q)) := by
    unfold F; linear_combination (Qs - Q) * h
  have : 0 < (a - s) * ((Gam D Qs - Gam D Q) - Q * (Phi D Qs - Phi D Q)) :=
    mul_pos (by linarith) (by linarith)
  linarith

lemma F_le (D : Demand) (s a w Qs Q : ℝ) (has : s < a) (hQs : 0 ≤ Qs) (hQ : 0 ≤ Q)
    (h : (a - w) - (a - s) * Phi D Qs = 0) :
    F D s a w Q ≤ F D s a w Qs := by
  rcases eq_or_ne Q Qs with e | e
  · rw [e]
  · exact (F_lt D s a w Qs Q has hQs hQ e h).le

end ChannelRebate.Quantity.Thm1Aux

open ChannelRebate.Quantity ChannelRebate.Quantity.Thm1Aux

theorem solution (p c s : ℝ) (hc : 0 < c) (hcp : c < p)
    (hsc : s < c) (D : Demand)
    (Qbar0 : ℝ) (hQbar0 : 0 < Qbar0) (hΦbar : Phi D Qbar0 = (p - c) / (p - s))
    (κ : ℝ) (hκ0 : 0 < κ) (hκπ : κ < (p - s) * Gam D Qbar0) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ε < κ →
      ∃! x : ℝ × ℝ × ℝ,
        -- the contract specification (1)–(3), with x = (w, u, T)
        ((∃ Q0 : ℝ, 0 ≤ Q0 ∧ Phi D Q0 = (p - x.1) / (p - s) ∧
            wholesaleProfit p s x.1 D Q0 = κ - ε) ∧
          x.2.1 = uHat p c s x.1 ∧
          0 ≤ x.2.2 ∧
          (p + x.2.1 - s) * Gam D Qbar0
            - x.2.1 * (Gam D x.2.2 + x.2.2 * (1 - Phi D x.2.2)) = κ) ∧
        -- (a)
        (c < x.1 ∧ x.1 < p ∧ 0 < x.2.1 ∧ 0 < x.2.2) ∧
        -- (b) channel coordination
        optimalOrders (retailerProfit p s x.1 x.2.1 x.2.2 D) = {Qbar0} ∧
        -- (c)
        retailerProfit p s x.1 x.2.1 x.2.2 D Qbar0 = κ ∧
        manufProfit c x.1 x.2.1 x.2.2 D Qbar0 = (p - s) * Gam D Qbar0 - κ := by
  have hps : 0 < p - s := by linarith
  have hcs : 0 < c - s := by linarith
  refine ⟨1, one_pos, fun ε hε _ hεκ => ?_⟩
  have e1 : (p - s) * Phi D Qbar0 = p - c := by
    rw [hΦbar]; field_simp
  -- Step 1: the wholesale price
  have hΓbar : (κ - ε) / (p - s) < Gam D Qbar0 := by
    rw [div_lt_iff₀ hps]; linarith
  obtain ⟨Q0, ⟨hQ0pos, hQ0lt⟩, hQ0eq⟩ :=
    intermediate_value_Ioo hQbar0.le (gam_cont D).continuousOn
      (show (κ - ε) / (p - s) ∈ Set.Ioo (Gam D 0) (Gam D Qbar0) from
        ⟨by rw [gam_zero]; exact div_pos (by linarith) hps, hΓbar⟩)
  have hΓQ0 : (p - s) * Gam D Q0 = κ - ε := by
    rw [hQ0eq]; field_simp
  set w := p - (p - s) * Phi D Q0 with hw
  have hfrac0 : (p - w) - (p - s) * Phi D Q0 = 0 := by rw [hw]; ring
  have hΦQ0 : Phi D Q0 = (p - w) / (p - s) := by
    rw [eq_div_iff hps.ne']; linarith
  have hΦQ0pos : 0 < Phi D Q0 := by
    have := phi_strict D 0 Q0 le_rfl hQ0pos; rwa [phi_zero] at this
  have hΦlt : Phi D Q0 < Phi D Qbar0 := phi_strict D Q0 Qbar0 hQ0pos.le hQ0lt
  have hcw : c < w := by
    have := mul_lt_mul_of_pos_left hΦlt hps
    rw [hw]; linarith
  have hwp : w < p := by
    have := mul_pos hps hΦQ0pos
    rw [hw]; linarith
  set u := uHat p c s w with hu_def
  have hu : 0 < u := div_pos (mul_pos (by linarith) hps) hcs
  have e2 : u * (c - s) = (w - c) * (p - s) := by
    rw [hu_def, uHat]; field_simp
  have hfrac : (p + u - w) - (p + u - s) * Phi D Qbar0 = 0 := by
    have : (p - s) * ((p + u - w) - (p + u - s) * Phi D Qbar0) = 0 := by
      linear_combination (-(p + u - s)) * e1 + e2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hps.ne'
    · exact h
  -- Step 2: the target
  have hS_cont : Continuous fun T => (p + u - s) * Gam D Qbar0 - u * S D T := by
    unfold S
    have := phi_cont D; have := gam_cont D
    fun_prop
  have hΓbarpos : 0 < Gam D Qbar0 := by
    have := gam_strict D 0 Qbar0 le_rfl hQbar0; rwa [gam_zero] at this
  have hh0 : κ < (p + u - s) * Gam D Qbar0 - u * S D 0 := by
    unfold S; rw [gam_zero, phi_zero]
    nlinarith
  have hhQ : (p + u - s) * Gam D Qbar0 - u * S D Qbar0 < κ := by
    have hlt := F_lt D s p w Q0 Qbar0 (by linarith) hQ0pos.le hQbar0.le hQ0lt.ne' hfrac0
    rw [F_crit D s p w Q0 hfrac0] at hlt
    have : (p + u - s) * Gam D Qbar0 - u * S D Qbar0 = F D s p w Qbar0 := by
      unfold S F; linear_combination (-Qbar0) * hfrac
    linarith
  obtain ⟨T, ⟨hTpos, hTlt⟩, hTeq⟩ :=
    intermediate_value_Ioo' hQbar0.le hS_cont.continuousOn
      (show κ ∈ Set.Ioo _ _ from ⟨hhQ, hh0⟩)
  simp only at hTeq
  -- profits
  have hRbar : retailerProfit p s w u T D Qbar0 = κ := by
    rw [retailer_gt D p s w u T Qbar0 hTpos.le hTlt, F_crit D s (p + u) w Qbar0 hfrac, ← hTeq]
  have hRlt : ∀ Q, 0 ≤ Q → Q ≠ Qbar0 → retailerProfit p s w u T D Q < κ := by
    intro Q hQ hne
    rcases le_or_gt Q T with h | h
    · rw [retailer_le D p s w u T Q hQ h]
      have := F_le D s p w Q0 Q (by linarith) hQ0pos.le hQ hfrac0
      rw [F_crit D s p w Q0 hfrac0] at this
      linarith
    · rw [retailer_gt D p s w u T Q hTpos.le h]
      have := F_lt D s (p + u) w Qbar0 Q (by linarith) hQbar0.le hQ hne hfrac
      rw [F_crit D s (p + u) w Qbar0 hfrac] at this
      linarith
  refine ⟨(w, u, T), ⟨⟨⟨Q0, hQ0pos.le, hΦQ0, ?_⟩, rfl, hTpos.le, ?_⟩,
    ⟨hcw, hwp, hu, hTpos⟩, ?_, hRbar, ?_⟩, ?_⟩
  · show wholesaleProfit p s w D Q0 = κ - ε
    rw [wholesale_eq D p s w Q0 hQ0pos.le, F_crit D s p w Q0 hfrac0, hΓQ0]
  · show (p + u - s) * Gam D Qbar0 - u * (Gam D T + T * (1 - Phi D T)) = κ
    exact hTeq
  · show optimalOrders (retailerProfit p s w u T D) = {Qbar0}
    ext Q
    simp only [optimalOrders, IsOptimalOrder, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hQ, hmax⟩
      by_contra hne
      have := hmax Qbar0 hQbar0.le
      have := hRlt Q hQ hne
      linarith
    · rintro rfl
      refine ⟨hQbar0.le, fun Q' hQ' => ?_⟩
      rcases eq_or_ne Q' Q with e | e
      · rw [e]
      · rw [hRbar]; exact (hRlt Q' hQ' e).le
  · show manufProfit c w u T D Qbar0 = (p - s) * Gam D Qbar0 - κ
    unfold manufProfit
    rw [rebate_gt D Qbar0 T hTpos.le hTlt.le]
    unfold S at hTeq ⊢
    linear_combination (-1 : ℝ) * hTeq - Qbar0 * hfrac - Qbar0 * e1
  · rintro ⟨w', u', T'⟩ ⟨⟨⟨Q0', hQ0'nn, hΦ', hW'⟩, hu', hT'nn, hT'eq⟩, _⟩
    simp only at hΦ' hW' hu' hT'nn hT'eq
    have hfrac0' : (p - w') - (p - s) * Phi D Q0' = 0 := by
      rw [hΦ']; field_simp; ring
    rw [wholesale_eq D p s w' Q0' hQ0'nn, F_crit D s p w' Q0' hfrac0'] at hW'
    have hQeq : Q0' = Q0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := gam_strict D Q0' Q0 hQ0'nn h
        have := mul_lt_mul_of_pos_left this hps
        linarith
      · have := gam_strict D Q0 Q0' hQ0pos.le h
        have := mul_lt_mul_of_pos_left this hps
        linarith
    subst hQeq
    have hweq : w' = w := by linarith
    subst hweq
    have hueq : u' = u := hu'
    subst hueq
    have hST : S D T' = S D T := by
      unfold S
      have := hTeq; unfold S at this
      have h2 : u * (Gam D T' + T' * (1 - Phi D T')) = u * (Gam D T + T * (1 - Phi D T)) := by
        linarith
      exact mul_left_cancel₀ hu.ne' h2
    have hTeq' : T' = T := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := S_strict D T' T hT'nn h; linarith
      · have := S_strict D T T' hTpos.le h; linarith
    rw [hTeq']
