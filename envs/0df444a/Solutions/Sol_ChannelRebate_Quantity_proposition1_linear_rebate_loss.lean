-- Prove2me | solution 1 for ChannelRebate.Quantity.proposition1_linear_rebate_loss
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:34:51.158567+00:00
-- url     : https://prove2.me/submissions/8c0253ac-1f9d-4d72-93b3-7310d8d486d4

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

namespace ChannelRebate.Quantity.Thm1Aux

lemma retailer_ge (D : Demand) (p s w u T Q : ℝ) (hT : 0 ≤ T) (h : T ≤ Q) :
    retailerProfit p s w u T D Q = F D s (p + u) w Q - u * S D T := by
  unfold retailerProfit
  rw [base_eq D p s w Q (by linarith), rebate_gt D Q T hT h]
  unfold F S; ring

lemma F_add (D : Demand) (s a u w Q : ℝ) : F D s (a + u) w Q = F D s a w Q + u * S D Q := by
  unfold F S; ring

lemma S_zero (D : Demand) : S D 0 = 0 := by simp [S, gam_zero]

lemma S_cont (D : Demand) : Continuous (S D) := by
  unfold S
  have := phi_cont D; have := gam_cont D
  fun_prop

lemma S_mono (D : Demand) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : S D a ≤ S D b := by
  rcases eq_or_lt_of_le hab with e | e
  · rw [e]
  · exact (S_strict D a b ha e).le

lemma Q_lt_of_phi (D : Demand) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Phi D a < Phi D b) :
    a < b := by
  by_contra hle
  push_neg at hle
  rcases eq_or_lt_of_le hle with e | e
  · rw [e] at h; exact lt_irrefl _ h
  · have := phi_strict D b a hb e; linarith

end ChannelRebate.Quantity.Thm1Aux

open ChannelRebate.Quantity ChannelRebate.Quantity.Thm1Aux

lemma phi_tendsto (D : Demand) : Filter.Tendsto (Phi D) Filter.atTop (nhds 1) := by
  have h1 : ∫ x in Set.Ioi (0 : ℝ), D.φ x = 1 := by
    have hadd := integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) D.integrable_φ
    rw [Set.compl_Iic, D.integral_φ, integral_Iic_eq_integral_Iio] at hadd
    have hz : ∫ x in Set.Iio (0 : ℝ), D.φ x = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun x hx => D.φ_eq_zero_of_neg x hx)
    linarith
  have := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) D.integrable_φ.integrableOn
    Filter.tendsto_id
  rw [h1] at this
  exact this

theorem solution (p c s w u : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (hu : 0 < u) (D : Demand)
    (Qbar0 : ℝ) (hQbar0 : 0 < Qbar0) (hΦbar : Phi D Qbar0 = (p - c) / (p - s))
    (hcoord : optimalOrders (retailerProfit p s w u 0 D) = {Qbar0}) :
    manufProfit c w u 0 D Qbar0 < 0 := by
  have hps : 0 < p - s := by linarith
  have hpus : 0 < p + u - s := by linarith
  set t := (p + u - w) / (p + u - s) with ht
  have ht0 : 0 < t := div_pos (by linarith) hpus
  have ht1 : t < 1 := by rw [ht, div_lt_one hpus]; linarith
  -- find Q1 with Φ Q1 = t
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    ((phi_tendsto D).eventually (lt_mem_nhds ht1))
  set M' := max M 1
  have hM' : t < Phi D M' := hM M' (le_max_left _ _)
  obtain ⟨Q1, ⟨hQ1pos, _⟩, hQ1eq⟩ := intermediate_value_Ioo (show (0:ℝ) ≤ M' by positivity)
    (phi_cont D).continuousOn (show t ∈ Set.Ioo (Phi D 0) (Phi D M') from
      ⟨by rw [phi_zero]; exact ht0, hM'⟩)
  have hfr1 : (p + u - w) - (p + u - s) * Phi D Q1 = 0 := by
    rw [hQ1eq, ht]; field_simp; ring
  have hR : ∀ Q, 0 ≤ Q → retailerProfit p s w u 0 D Q = F D s (p + u) w Q := by
    intro Q hQ
    rw [retailer_ge D p s w u 0 Q le_rfl hQ, S_zero]; ring
  have hopt : Q1 ∈ optimalOrders (retailerProfit p s w u 0 D) := by
    refine ⟨hQ1pos.le, fun Q hQ => ?_⟩
    rw [hR Q hQ, hR Q1 hQ1pos.le]
    exact F_le D s (p + u) w Q1 Q (by linarith) hQ1pos.le hQ hfr1
  rw [hcoord, Set.mem_singleton_iff] at hopt
  subst hopt
  have e1 : (p - s) * Phi D Q1 = p - c := by rw [hΦbar]; field_simp
  have hΓ : 0 < Gam D Q1 := by
    have := gam_strict D 0 Q1 le_rfl hQ1pos; rwa [gam_zero] at this
  unfold manufProfit
  rw [rebate_gt D Q1 0 le_rfl hQ1pos.le, S_zero]
  unfold S
  have : (w - c) * Q1 - u * (Gam D Q1 + Q1 * (1 - Phi D Q1) - 0) = -u * Gam D Q1 := by
    linear_combination (-Q1) * hfr1 - Q1 * e1
  rw [this]
  nlinarith
