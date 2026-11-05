-- Prove2me | solution 1 for FVRPricing.DecayBalancing.kappa_strictAntiOn
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:46:52.603014+00:00
-- url     : https://prove2.me/submissions/d40c1d0f-5799-427d-a85c-f519fb1a392d

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies
import Definitions.Def_FVRPricing_DecayBalancing_Kappa

open MeasureTheory ProbabilityTheory FVRPricing.DecayBalancing Set Filter Topology

lemma fvrk_upper_rec (a : ℝ) (ha : 0 < a) :
    upperGamma (a + 1) a = a ^ a * Real.exp (-a) + a * upperGamma a a := by
  unfold upperGamma
  have hsub : Ioi a ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi ha.le
  have hI1 : IntegrableOn (fun t : ℝ => t ^ a * Real.exp (-t)) (Ioi a) := by
    refine ((Real.GammaIntegral_convergent (by linarith : (0 : ℝ) < a + 1)).mono_set hsub).congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    simp only [add_sub_cancel_right]; ring
  have hI2 : IntegrableOn (fun t : ℝ => a * t ^ (a - 1) * -Real.exp (-t)) (Ioi a) := by
    have h0 : IntegrableOn (fun t : ℝ => -a * (Real.exp (-t) * t ^ (a - 1))) (Ioi a) :=
      ((Real.GammaIntegral_convergent ha).mono_set hsub).const_mul (-a)
    refine h0.congr_fun (fun t _ => ?_) measurableSet_Ioi
    ring
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := a) (a' := a ^ a * -Real.exp (-a)) (b' := 0)
    (u := fun t : ℝ => t ^ a) (u' := fun t => a * t ^ (a - 1))
    (v := fun t : ℝ => -Real.exp (-t)) (v' := fun t => Real.exp (-t))
    (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_trans ha hx))))
    (fun x _ => by
      have := ((hasDerivAt_neg x).exp).neg
      simp only [mul_neg, mul_one, neg_neg] at this
      exact this)
    hI1 hI2
    (by
      have hc : ContinuousAt (fun t : ℝ => t ^ a * -Real.exp (-t)) a :=
        (Real.continuousAt_rpow_const _ _ (Or.inl ha.ne')).mul (by fun_prop)
      exact hc.tendsto.mono_left nhdsWithin_le_nhds)
    (by
      have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a 1 one_pos).neg
      rw [neg_zero] at this
      have hfun : ((fun t : ℝ => t ^ a) * fun t => -Real.exp (-t)) =
          fun x => -(x ^ a * Real.exp (-1 * x)) := by
        funext x; simp only [Pi.mul_apply, neg_one_mul, mul_neg]
      rw [hfun]; exact this)
  have e1 : (fun t : ℝ => t ^ (a + 1 - 1) * Real.exp (-t)) = fun t => t ^ a * Real.exp (-t) := by
    funext t; simp only [add_sub_cancel_right]
  rw [e1, key]
  have e2 : ∫ x in Ioi a, a * x ^ (a - 1) * -Real.exp (-x) =
      -(a * ∫ x in Ioi a, x ^ (a - 1) * Real.exp (-x)) := by
    rw [← integral_const_mul, ← integral_neg]
    congr 1; funext x; ring
  rw [e2]; ring

lemma fvrk_upper_nonneg (s y : ℝ) (hy : 0 ≤ y) : 0 ≤ upperGamma s y := by
  unfold upperGamma
  refine setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_)
  exact mul_nonneg (Real.rpow_nonneg (le_trans hy (le_of_lt ht)) _) (Real.exp_pos _).le

lemma fvrk_lt_Gamma (a : ℝ) (ha : 0 < a) : a ^ a * Real.exp (-a) < Real.Gamma (a + 1) := by
  rw [Real.Gamma_eq_integral (by linarith), ← Ioc_union_Ioi_eq_Ioi ha.le]
  have hint := Real.GammaIntegral_convergent (by linarith : (0 : ℝ) < a + 1)
  rw [← Ioc_union_Ioi_eq_Ioi ha.le] at hint
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set subset_union_left) (hint.mono_set subset_union_right)]
  have h1 : 0 < ∫ x in Ioc 0 a, Real.exp (-x) * x ^ (a + 1 - 1) := by
    rw [← intervalIntegral.integral_of_le ha.le]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) ha
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le]
      exact hint.mono_set subset_union_left
    · exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hx.1 _)
  have h2 : ∫ x in Ioi a, Real.exp (-x) * x ^ (a + 1 - 1) = upperGamma (a + 1) a := by
    unfold upperGamma; congr 1; funext x; ring
  rw [h2, fvrk_upper_rec a ha]
  have := fvrk_upper_nonneg a a ha.le
  nlinarith

/-- `φ(a) = a log a − a − log Γ(a+1)`. -/
lemma fvrk_phi_step (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb1 : b ≤ a + 1) :
    b * Real.log b - b - Real.log (Real.Gamma (b + 1)) <
      a * Real.log a - a - Real.log (Real.Gamma (a + 1)) := by
  have hb : 0 < b := lt_trans ha hab
  have hconv := Real.convexOn_log_Gamma
  have hsec := hconv.secant_mono (a := b + 1) (x := b) (y := a + 1)
    (by simp only [mem_Ioi]; linarith) (by simpa using hb) (by simp only [mem_Ioi]; linarith)
    (by linarith) (by linarith) hb1
  simp only [Function.comp_apply] at hsec
  have hG : Real.log (Real.Gamma (b + 1)) = Real.log b + Real.log (Real.Gamma b) := by
    rw [Real.Gamma_add_one hb.ne', Real.log_mul hb.ne' (Real.Gamma_pos_of_pos hb).ne']
  rw [hG, show b - (b + 1) = -1 by ring, show a + 1 - (b + 1) = a - b by ring] at hsec
  have hlb : Real.log b * (b - a) ≤
      Real.log b + Real.log (Real.Gamma b) - Real.log (Real.Gamma (a + 1)) := by
    have hneg : a - b < 0 := by linarith
    rw [le_div_iff_of_neg hneg] at hsec
    have : (Real.log (Real.Gamma b) - (Real.log b + Real.log (Real.Gamma b))) / -1 = Real.log b := by
      ring
    rw [this] at hsec
    nlinarith
  have hlog : Real.log (b / a) < b / a - 1 :=
    Real.log_lt_sub_one_of_pos (div_pos hb ha) (by
      intro h; rw [div_eq_one_iff_eq ha.ne'] at h; linarith)
  rw [Real.log_div hb.ne' ha.ne'] at hlog
  have h3 : a * (Real.log b - Real.log a) < a * (b / a - 1) := mul_lt_mul_of_pos_left hlog ha
  have h4 : a * (b / a - 1) = b - a := by field_simp
  rw [h4] at h3
  rw [hG]
  nlinarith

lemma fvrk_phi_anti (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    b * Real.log b - b - Real.log (Real.Gamma (b + 1)) <
      a * Real.log a - a - Real.log (Real.Gamma (a + 1)) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (b - a)
  have P : ∀ n : ℕ, ∀ a b : ℝ, 0 < a → a < b → b ≤ a + (n + 1) →
      b * Real.log b - b - Real.log (Real.Gamma (b + 1)) <
        a * Real.log a - a - Real.log (Real.Gamma (a + 1)) := by
    intro n
    induction n with
    | zero =>
      intro a b ha hab hb
      exact fvrk_phi_step a b ha hab (by simpa using hb)
    | succ n ih =>
      intro a b ha hab hb
      by_cases h1 : b ≤ a + 1
      · exact fvrk_phi_step a b ha hab h1
      · push Not at h1
        have hc1 := ih a (b - 1) ha (by linarith) (by push_cast at hb ⊢; linarith)
        have hc2 := fvrk_phi_step (b - 1) b (by linarith) (by linarith) (by linarith)
        linarith
  exact P n a b ha hab (by linarith)

lemma fvrk_kappa_eq (a : ℝ) (ha : 0 < a) :
    kappa a = 1 / (1 - Real.exp (a * Real.log a - a - Real.log (Real.Gamma (a + 1)))) := by
  unfold kappa
  have hG := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < a + 1)
  have hlt := fvrk_lt_Gamma a ha
  have hrec := fvrk_upper_rec a ha
  have hden : Real.Gamma (a + 1) - upperGamma (a + 1) a + a * upperGamma a a =
      Real.Gamma (a + 1) - a ^ a * Real.exp (-a) := by rw [hrec]; ring
  have hexp : Real.exp (a * Real.log a - a - Real.log (Real.Gamma (a + 1))) =
      a ^ a * Real.exp (-a) / Real.Gamma (a + 1) := by
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log hG, Real.rpow_def_of_pos ha, mul_comm a,
      Real.exp_neg]
    field_simp
  rw [hden, hexp, ← Real.Gamma_add_one ha.ne']
  have hne : Real.Gamma (a + 1) - a ^ a * Real.exp (-a) ≠ 0 := by linarith
  field_simp

theorem solution : StrictAntiOn kappa (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  rw [fvrk_kappa_eq a ha, fvrk_kappa_eq b hb]
  have hqa : Real.exp (a * Real.log a - a - Real.log (Real.Gamma (a + 1))) < 1 := by
    have hG := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < a + 1)
    have hlt := fvrk_lt_Gamma a ha
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log hG, Real.rpow_def_of_pos ha, mul_comm a,
      Real.exp_neg] at *
    rw [div_lt_one hG]
    have : Real.exp (Real.log a * a) / Real.exp a = Real.exp (Real.log a * a) * (Real.exp a)⁻¹ := by
      ring
    linarith
  have hmono := Real.exp_lt_exp.mpr (fvrk_phi_anti a b ha hab)
  have hpos : 0 < 1 - Real.exp (a * Real.log a - a - Real.log (Real.Gamma (a + 1))) := by linarith
  apply one_div_lt_one_div_of_lt hpos
  linarith
