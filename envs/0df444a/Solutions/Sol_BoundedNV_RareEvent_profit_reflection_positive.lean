-- Prove2me | solution 1 for BoundedNV.RareEvent.profit_reflection_positive
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:59:44.549721+00:00
-- url     : https://prove2.me/submissions/0f67c5e7-fa0e-4e63-8056-06b53f63d693

import Mathlib
import Definitions.Def_BoundedNV_RareEvent_Logit

open MeasureTheory Set BoundedNV.Uniform

private lemma min_density_integrable (f : ℝ → ℝ) (hf : BoundedNV.ExpFam.IsDemandDensity f)
    (x : ℝ) (hx : 0 ≤ x) : Integrable (fun t => min t x * f t) := by
  apply (hf.integrable.const_mul x).mono'
    ((continuous_id.min continuous_const).aestronglyMeasurable.mul hf.integrable.aestronglyMeasurable)
  filter_upwards with t
  change ‖min t x*f t‖ ≤ x*f t
  by_cases ht : t < 0
  · simp [hf.zero_of_neg t ht, hx]
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_min (le_of_not_gt ht) hx) (hf.nonneg t))]
    exact mul_le_mul_of_nonneg_right (min_le_right t x) (hf.nonneg t)

theorem solution (f : ℝ → ℝ) (p c a b y : ℝ)
    (hf : BoundedNV.ExpFam.IsDemandDensity f) (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ x ∉ Set.Icc a b, f x = 0)
    (hp : 0 < p) (hy : 0 < y) (hyr : y ≤ (b - a) / 2)
    (hfractile : c = p * (1 - BoundedNV.Uniform.demandCDF f ((a + b) / 2)))
    (hanti : StrictAntiOn f (Set.Icc a b)) :
    BoundedNV.Uniform.nvProfit f p c ((a + b) / 2 - y) <
      BoundedNV.Uniform.nvProfit f p c ((a + b) / 2 + y) := by
  let m := (a+b)/2
  have hlo : a ≤ m-y := by dsimp [m]; linarith
  have hhi : m+y ≤ b := by dsimp [m]; linarith
  have hmin : 0 ≤ m-y := ha.trans hlo
  have hplus : 0 ≤ m+y := by linarith
  have hiL : IntervalIntegrable (fun t => (t-(m-y))*f t) volume (m-y) m :=
    hf.integrable.intervalIntegrable.continuousOn_mul (by fun_prop)
  have hiR : IntervalIntegrable (fun t => (m+y-t)*f t) volume m (m+y) :=
    hf.integrable.intervalIntegrable.continuousOn_mul (by fun_prop)
  have hiLi : Integrable ((Ioc (m-y) m).indicator (fun t => (t-(m-y))*f t)) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    simpa [uIoc_of_le (show m-y ≤ m by linarith)] using hiL.def'
  have hiRi : Integrable ((Ioc m (m+y)).indicator (fun t => (m+y-t)*f t)) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    simpa [uIoc_of_le (show m ≤ m+y by linarith)] using hiR.def'
  have htail : (∫ t in Ioi m, f t) = 1-demandCDF f m := by
    have ht := integral_add_compl measurableSet_Iic hf.integrable (s := Iic m)
    rw [compl_Iic, hf.integral_eq_one] at ht
    dsimp [demandCDF]
    linarith
  have he (t : ℝ) : min t (m+y)*f t-min t (m-y)*f t-
      (Ioi m).indicator (fun t => 2*y*f t) t =
      (Ioc (m-y) m).indicator (fun t => (t-(m-y))*f t) t -
      (Ioc m (m+y)).indicator (fun t => (m+y-t)*f t) t := by
    by_cases htL : t ≤ m-y
    · have ht : t ≤ m := by linarith
      simp [min_eq_left htL, min_eq_left (show t ≤ m+y by linarith),
        show t ∉ Ioi m by simpa, show t ∉ Ioc (m-y) m by intro h; linarith [h.1, h.2],
        show t ∉ Ioc m (m+y) by intro h; linarith [h.1, h.2]]
    · have htL' : m-y ≤ t := (lt_of_not_ge htL).le
      by_cases ht : t ≤ m
      · simp [min_eq_right htL', min_eq_left (show t ≤ m+y by linarith),
          show t ∉ Ioi m by simpa, show t ∈ Ioc (m-y) m from ⟨lt_of_not_ge htL, ht⟩,
          show t ∉ Ioc m (m+y) by intro h; linarith [h.1, h.2]]
        ring
      · have htm : m < t := lt_of_not_ge ht
        by_cases htU : t ≤ m+y
        · simp [min_eq_right htL', min_eq_left htU,
            show t ∈ Ioi m from htm, show t ∉ Ioc (m-y) m by intro h; linarith [h.1, h.2],
            show t ∈ Ioc m (m+y) from ⟨htm, htU⟩]
          ring
        · simp [min_eq_right htL', min_eq_right (le_of_not_ge htU),
            show t ∈ Ioi m from htm, show t ∉ Ioc (m-y) m by intro h; linarith [h.1, h.2],
            show t ∉ Ioc m (m+y) by intro h; linarith [h.1, h.2]]
          ring
  have hdelta : expMin f (m+y)-expMin f (m-y)-2*y*(1-demandCDF f m) =
      (∫ t in (m-y)..m, (t-(m-y))*f t) - ∫ t in m..(m+y), (m+y-t)*f t := by
    have hiT : Integrable ((Ioi m).indicator (fun t => 2*y*f t)) :=
      (hf.integrable.const_mul _).indicator measurableSet_Ioi
    have hi1 := min_density_integrable f hf (m+y) hplus
    have hi2 := min_density_integrable f hf (m-y) hmin
    have hi12 : Integrable (fun t => min t (m+y)*f t-min t (m-y)*f t) := by
      simpa only [Pi.sub_def] using hi1.sub hi2
    have hh := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall he)
    rw [integral_sub hi12 hiT, integral_sub hi1 hi2,
      integral_sub hiLi hiRi, integral_indicator measurableSet_Ioi,
      integral_const_mul, htail, integral_indicator measurableSet_Ioc,
      integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le (show m-y ≤ m by linarith),
      ← intervalIntegral.integral_of_le (show m ≤ m+y by linarith)] at hh
    exact hh
  have hmono : MonotoneOn (fun t => f (2*m-t)) (uIcc m (m+y)) := by
    rw [uIcc_of_le (show m ≤ m+y by linarith)]
    intro s hs t ht hst
    apply hanti.antitoneOn
    · constructor <;> linarith [ht.1, ht.2]
    · constructor <;> linarith [hs.1, hs.2]
    · linarith
  have hiRef : IntervalIntegrable (fun t => (m+y-t)*f (2*m-t)) volume m (m+y) :=
    hmono.intervalIntegrable.continuousOn_mul (by fun_prop)
  have href : (∫ t in (m-y)..m, (t-(m-y))*f t) =
      ∫ t in m..(m+y), (m+y-t)*f (2*m-t) := by
    have ht := intervalIntegral.integral_comp_sub_left (fun t => (t-(m-y))*f t)
      (a := m) (b := m+y) (2*m)
    simp only [show 2*m-(m+y) = m-y by ring, show 2*m-m = m by ring] at ht
    rw [← ht]
    apply intervalIntegral.integral_congr
    intro t ht
    congr 1 <;> ring
  have hpos : 0 < ∫ t in m..(m+y), (m+y-t)*(f (2*m-t)-f t) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hiRef.sub hiR |>.congr (by intro t ht; ring))
    · intro t ht
      apply mul_pos (by linarith [ht.2])
      apply sub_pos.mpr
      apply hanti
      · constructor <;> linarith [ht.1, ht.2]
      · constructor <;> linarith [ht.1, ht.2]
      · linarith [ht.1]
    · linarith
  have hid : (∫ t in m..(m+y), (m+y-t)*(f (2*m-t)-f t)) =
      (∫ t in m..(m+y), (m+y-t)*f (2*m-t)) - ∫ t in m..(m+y), (m+y-t)*f t := by
    rw [← intervalIntegral.integral_sub hiRef hiR]
    apply intervalIntegral.integral_congr
    intro t ht; ring
  rw [hid, ← href, ← hdelta] at hpos
  unfold nvProfit
  change p*expMin f (m-y)-c*(m-y) < p*expMin f (m+y)-c*(m+y)
  change c = p*(1-demandCDF f m) at hfractile
  rw [hfractile]
  nlinarith [mul_pos hp hpos]

#print axioms solution
