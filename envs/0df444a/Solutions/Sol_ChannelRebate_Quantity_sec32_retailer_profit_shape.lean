-- Prove2me | solution 1 for ChannelRebate.Quantity.sec32_retailer_profit_shape
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:38:05.417266+00:00
-- url     : https://prove2.me/submissions/f5b247e1-7df2-45ed-a10d-f2711efdd593

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


open Filter Topology

namespace ChannelRebate.Quantity.Thm1Aux

open CachonCoord.Newsvendor

lemma phi_nonpos (D : Demand) (Q : ℝ) (hQ : Q ≤ 0) : Phi D Q = 0 := by
  unfold Phi
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hQ,
    integral_Ioc_eq_integral_Ioo,
    setIntegral_eq_zero_of_forall_eq_zero (fun x hx => D.φ_eq_zero_of_neg x hx.2)]
  simp

lemma gam_nonpos (D : Demand) (Q : ℝ) (hQ : Q ≤ 0) : Gam D Q = 0 := by
  unfold Gam
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hQ,
    integral_Ioc_eq_integral_Ioo,
    setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by rw [D.φ_eq_zero_of_neg x hx.2, mul_zero])]
  simp

lemma L_int (D : Demand) (Q : ℝ) : ∫ x in (0:ℝ)..Q, (Q - x) * D.φ x = Q * Phi D Q - Gam D Q := by
  unfold Phi Gam
  have e : (fun x => (Q - x) * D.φ x) = fun x => Q * D.φ x - x * D.φ x := by ext; ring
  rw [e, intervalIntegral.integral_sub ((ii_phi D 0 Q).const_mul Q) (ii_xphi D 0 Q),
    intervalIntegral.integral_const_mul]

lemma leftover_all (D : Demand) (Q : ℝ) : expLeftover D.law Q = Q * Phi D Q - Gam D Q := by
  rcases le_total 0 Q with h | h
  · exact leftover_eq D Q h
  · rw [phi_nonpos D Q h, gam_nonpos D Q h]
    unfold expLeftover
    rw [integral_law]
    have : (fun x => D.φ x * max (Q - x) 0) = fun _ => (0:ℝ) := by
      ext x
      rcases lt_or_ge x 0 with hx | hx
      · rw [D.φ_eq_zero_of_neg x hx, zero_mul]
      · rw [max_eq_right (by linarith), mul_zero]
    rw [this, integral_zero]; ring

lemma sales_all (D : Demand) (Q : ℝ) : expSales D.law Q = S D Q := by
  have h1 := leftover_all D Q
  unfold expLeftover at h1
  rw [integral_law, leftover_aux] at h1
  unfold expSales S
  rw [integral_law]
  linarith

lemma base_all (D : Demand) (p s w Q : ℝ) :
    -w * Q + p * expSales D.law Q + s * expLeftover D.law Q = F D s p w Q := by
  rw [sales_all D Q, leftover_all D Q]
  unfold S F; ring

lemma S_mono_all (D : Demand) : Monotone (S D) := by
  intro a b hab
  have hSn : ∀ Q, Q ≤ 0 → S D Q = Q := fun Q hQ => by
    unfold S; rw [phi_nonpos D Q hQ, gam_nonpos D Q hQ]; ring
  rcases le_total 0 a with ha | ha
  · exact S_mono D a b ha hab
  · rcases le_total b 0 with hb | hb
    · rw [hSn a ha, hSn b hb]; exact hab
    · rw [hSn a ha]
      have := S_mono D 0 b le_rfl hb
      rw [hSn 0 le_rfl] at this; linarith

lemma rebate_all (D : Demand) (Q T : ℝ) (hT : 0 ≤ T) :
    rebateUnits D Q T = max (S D Q - S D T) 0 := by
  rcases le_total Q T with h | h
  · rw [rebate_le D Q T h, max_eq_right (by linarith [S_mono_all D h])]
  · rw [rebate_gt D Q T hT h, max_eq_left (by linarith [S_mono_all D h])]

lemma retailer_all (D : Demand) (p s w u T Q : ℝ) (hT : 0 ≤ T) :
    retailerProfit p s w u T D Q = F D s p w Q + u * max (S D Q - S D T) 0 := by
  unfold retailerProfit
  rw [base_all, rebate_all D Q T hT]

/-- `G(Q) = QΦ(Q) − Γ(Q) = ∫₀^Q (Q − x) φ`. -/
noncomputable def G (D : Demand) (Q : ℝ) : ℝ := Q * Phi D Q - Gam D Q

lemma G_bound (D : Demand) (x y : ℝ) :
    |G D y - G D x - (y - x) * Phi D x| ≤ |y - x| * |Phi D y - Phi D x| := by
  have hrepr : G D y - G D x - (y - x) * Phi D x = ∫ t in x..y, (y - t) * D.φ t := by
    have e : (fun t => (y - t) * D.φ t) = fun t => y * D.φ t - t * D.φ t := by ext; ring
    rw [e, intervalIntegral.integral_sub ((ii_phi D x y).const_mul y) (ii_xphi D x y),
      intervalIntegral.integral_const_mul, ← phi_sub, ← gam_sub]
    unfold G; ring
  have hii : ∀ a b k : ℝ, IntervalIntegrable (fun t => (k - t) * D.φ t) volume a b := by
    intro a b k
    exact (((ii_phi D a b).const_mul k).sub (ii_xphi D a b)).congr (fun t _ => by ring)
  rw [hrepr]
  rcases le_total x y with h | h
  · have h0 : 0 ≤ ∫ t in x..y, (y - t) * D.φ t :=
      intervalIntegral.integral_nonneg h (fun t ht => mul_nonneg (by linarith [ht.2]) (phi_nonneg D t))
    have h1 : ∫ t in x..y, (y - t) * D.φ t ≤ ∫ t in x..y, (y - x) * D.φ t :=
      intervalIntegral.integral_mono_on h (hii x y y) ((ii_phi D x y).const_mul _)
        (fun t ht => mul_le_mul_of_nonneg_right (by linarith [ht.1]) (phi_nonneg D t))
    rw [intervalIntegral.integral_const_mul, ← phi_sub] at h1
    have hΦ : 0 ≤ Phi D y - Phi D x := by
      rw [phi_sub]; exact intervalIntegral.integral_nonneg h (fun t _ => phi_nonneg D t)
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith), abs_of_nonneg hΦ]
    exact h1
  · rw [intervalIntegral.integral_symm]
    have e2 : ∫ t in y..x, (y - t) * D.φ t = - ∫ t in y..x, (t - y) * D.φ t := by
      rw [← intervalIntegral.integral_neg]; congr 1; ext t; ring
    rw [e2, neg_neg]
    have h0 : 0 ≤ ∫ t in y..x, (t - y) * D.φ t :=
      intervalIntegral.integral_nonneg h (fun t ht => mul_nonneg (by linarith [ht.1]) (phi_nonneg D t))
    have hii2 : IntervalIntegrable (fun t => (t - y) * D.φ t) volume y x :=
      ((ii_xphi D y x).sub ((ii_phi D y x).const_mul y)).congr (fun t _ => by ring)
    have h1 : ∫ t in y..x, (t - y) * D.φ t ≤ ∫ t in y..x, (x - y) * D.φ t :=
      intervalIntegral.integral_mono_on h hii2 ((ii_phi D y x).const_mul _)
        (fun t ht => mul_le_mul_of_nonneg_right (by linarith [ht.2]) (phi_nonneg D t))
    rw [intervalIntegral.integral_const_mul, ← phi_sub] at h1
    have hΦ : 0 ≤ Phi D x - Phi D y := by
      rw [phi_sub]; exact intervalIntegral.integral_nonneg h (fun t _ => phi_nonneg D t)
    rw [abs_of_nonneg h0, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    nlinarith

lemma G_deriv (D : Demand) (x : ℝ) : HasDerivAt (G D) (Phi D x) x := by
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  have hca := (phi_cont D).continuousAt (x := x)
  rw [Metric.continuousAt_iff'] at hca
  filter_upwards [hca c hc] with y hy
  rw [Real.dist_eq] at hy
  simp only [Real.norm_eq_abs, smul_eq_mul]
  calc |G D y - G D x - (y - x) * Phi D x| ≤ |y - x| * |Phi D y - Phi D x| := G_bound D x y
    _ ≤ |y - x| * c := mul_le_mul_of_nonneg_left hy.le (abs_nonneg _)
    _ = c * |y - x| := by ring

lemma F_eq_G (D : Demand) (s a w Q : ℝ) : F D s a w Q = (a - w) * Q - (a - s) * G D Q := by
  unfold F G; ring

lemma F_deriv (D : Demand) (s a w Q : ℝ) :
    HasDerivAt (F D s a w) ((a - w) - (a - s) * Phi D Q) Q := by
  have : F D s a w = fun Q => (a - w) * Q - (a - s) * G D Q := by
    ext Q; exact F_eq_G D s a w Q
  rw [this]
  have h1 : HasDerivAt (fun y => (a - w) * y) (a - w) Q := by
    simpa using (hasDerivAt_id Q).const_mul (a - w)
  exact h1.sub ((G_deriv D Q).const_mul (a - s))

lemma G_cont (D : Demand) : Continuous (G D) := by
  unfold G; have := phi_cont D; have := gam_cont D; fun_prop

lemma G_strictConvex (D : Demand) : StrictConvexOn ℝ (Set.Ici 0) (G D) := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) (G_cont D).continuousOn
  rw [interior_Ici]
  intro a ha b hb hab
  rw [(G_deriv D a).deriv, (G_deriv D b).deriv]
  exact phi_strict D a b (le_of_lt ha) hab

lemma concave_of_G (D : Demand) (K M C : ℝ) (hM : 0 < M) (f : ℝ → ℝ) (U : Set ℝ)
    (hU : Convex ℝ U) (hsub : U ⊆ Set.Ici 0) (hf : ∀ Q ∈ U, f Q = K * Q - M * G D Q + C) :
    StrictConcaveOn ℝ U f := by
  refine ⟨hU, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have h := (G_strictConvex D).2 (hsub hx) (hsub hy) hxy ha hb hab
  have hm := hU hx hy ha.le hb.le hab
  simp only [smul_eq_mul] at h hm ⊢
  rw [hf x hx, hf y hy, hf _ hm]
  have h2 := mul_lt_mul_of_pos_left h hM
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith

end ChannelRebate.Quantity.Thm1Aux

open ChannelRebate.Quantity ChannelRebate.Quantity.Thm1Aux

theorem solution (p c s w u T : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (hu : 0 < u) (hT : 0 ≤ T) (D : Demand) :
    -- the two closed forms
    (∀ Q : ℝ, 0 ≤ Q → Q ≤ T →
      retailerProfit p s w u T D Q =
        (p - w) * Q - (p - s) * ∫ x in (0 : ℝ)..Q, (Q - x) * D.φ x) ∧
    (∀ Q : ℝ, T < Q →
      retailerProfit p s w u T D Q =
        (p - w) * Q - (p - s) * (∫ x in (0 : ℝ)..Q, (Q - x) * D.φ x)
          + u * ((∫ x in T..Q, (x - T) * D.φ x) + (Q - T) * (1 - Phi D Q))) ∧
    -- the derivative on each piece
    (∀ Q : ℝ, 0 < Q → Q < T →
      HasDerivAt (retailerProfit p s w u T D) (p - w - (p - s) * Phi D Q) Q) ∧
    (∀ Q : ℝ, T < Q →
      HasDerivAt (retailerProfit p s w u T D) (p + u - w - (p + u - s) * Phi D Q) Q) ∧
    -- strict concavity on each piece
    StrictConcaveOn ℝ (Set.Ico 0 T) (retailerProfit p s w u T D) ∧
    StrictConcaveOn ℝ (Set.Ioi T) (retailerProfit p s w u T D) ∧
    -- continuity
    Continuous (retailerProfit p s w u T D) ∧
    -- the kink: the left limit of the derivative at T is below the right limit
    Tendsto (deriv (retailerProfit p s w u T D)) (𝓝[<] T)
      (𝓝 (p - w - (p - s) * Phi D T)) ∧
    Tendsto (deriv (retailerProfit p s w u T D)) (𝓝[>] T)
      (𝓝 (p + u - w - (p + u - s) * Phi D T)) ∧
    p - w - (p - s) * Phi D T < p + u - w - (p + u - s) * Phi D T := by
  have hps : 0 < p - s := by linarith
  have hpus : 0 < p + u - s := by linarith
  set R := retailerProfit p s w u T D with hR
  have hRle : ∀ Q, Q ≤ T → R Q = F D s p w Q := by
    intro Q hQ
    rw [hR, retailer_all D p s w u T Q hT, max_eq_right (by linarith [S_mono_all D hQ])]; ring
  have hRge : ∀ Q, T ≤ Q → R Q = F D s (p + u) w Q - u * S D T := by
    intro Q hQ
    rw [hR, retailer_all D p s w u T Q hT, max_eq_left (by linarith [S_mono_all D hQ]), F_add]; ring
  -- derivatives
  have hdl : ∀ Q, Q < T → HasDerivAt R (p - w - (p - s) * Phi D Q) Q := by
    intro Q hQ
    refine (F_deriv D s p w Q).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hQ] with y hy
    exact hRle y (le_of_lt hy)
  have hdr : ∀ Q, T < Q → HasDerivAt R (p + u - w - (p + u - s) * Phi D Q) Q := by
    intro Q hQ
    have := (F_deriv D s (p + u) w Q).sub_const (u * S D T)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hQ] with y hy
    exact hRge y (le_of_lt hy)
  have hΦT : Phi D T < 1 := lt_of_lt_of_le (phi_strict D T (T + 1) hT (by linarith))
    (phi_le_one D (T + 1) (by linarith))
  refine ⟨?_, ?_, fun Q _ hQ => hdl Q hQ, hdr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q _ hQT
    rw [hRle Q hQT, L_int]; unfold F; ring
  · intro Q hQ
    rw [hRge Q hQ.le, L_int]
    have e : ∫ x in T..Q, (x - T) * D.φ x = (Gam D Q - Gam D T) - T * (Phi D Q - Phi D T) := by
      rw [gam_sub, phi_sub, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (ii_xphi D T Q) ((ii_phi D T Q).const_mul T)]
      congr 1; ext x; ring
    rw [e]; unfold F S; ring
  · refine concave_of_G D (p - w) (p - s) 0 hps R _ (convex_Ico 0 T)
      (fun x hx => hx.1) (fun Q hQ => ?_)
    rw [hRle Q hQ.2.le, F_eq_G]; ring
  · refine concave_of_G D (p + u - w) (p + u - s) (-(u * S D T)) hpus R _ (convex_Ioi T)
      (fun x hx => le_of_lt (lt_of_le_of_lt hT hx)) (fun Q hQ => ?_)
    rw [hRge Q (le_of_lt hQ), F_eq_G]; ring
  · have : R = fun Q => F D s p w Q + u * max (S D Q - S D T) 0 := by
      ext Q; exact retailer_all D p s w u T Q hT
    rw [this]
    have h1 : Continuous (F D s p w) := by
      unfold F; have := phi_cont D; have := gam_cont D; fun_prop
    have h2 := S_cont D
    fun_prop
  · have hc : Continuous fun Q => p - w - (p - s) * Phi D Q := by
      have := phi_cont D; fun_prop
    refine Tendsto.congr' ?_ (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((hdl y hy).deriv).symm
  · have hc : Continuous fun Q => p + u - w - (p + u - s) * Phi D Q := by
      have := phi_cont D; fun_prop
    refine Tendsto.congr' ?_ (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((hdr y hy).deriv).symm
  · nlinarith
