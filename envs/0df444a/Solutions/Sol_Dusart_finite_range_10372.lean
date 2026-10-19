-- Prove2me | solution 1 for Dusart.finite_range_10372
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:49.380073+00:00
-- url     : https://prove2.me/submissions/5dda3a9c-4ec0-4c19-b932-c17e87e83796

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.NormNum.Prime
import Theorems.Thm_DusartCert_run_0
import Theorems.Thm_DusartCert_run_1
import Theorems.Thm_DusartCert_run_10
import Theorems.Thm_DusartCert_run_11
import Theorems.Thm_DusartCert_run_12
import Theorems.Thm_DusartCert_run_13
import Theorems.Thm_DusartCert_run_14
import Theorems.Thm_DusartCert_run_15
import Theorems.Thm_DusartCert_run_16
import Theorems.Thm_DusartCert_run_17
import Theorems.Thm_DusartCert_run_18
import Theorems.Thm_DusartCert_run_19
import Theorems.Thm_DusartCert_run_2
import Theorems.Thm_DusartCert_run_20
import Theorems.Thm_DusartCert_run_21
import Theorems.Thm_DusartCert_run_22
import Theorems.Thm_DusartCert_run_23
import Theorems.Thm_DusartCert_run_3
import Theorems.Thm_DusartCert_run_4
import Theorems.Thm_DusartCert_run_5
import Theorems.Thm_DusartCert_run_6
import Theorems.Thm_DusartCert_run_7
import Theorems.Thm_DusartCert_run_8
import Theorems.Thm_DusartCert_run_9

section

open Finset Real MeasureTheory Set

set_option autoImplicit false

namespace Dusart

/-- `∑_{p ≤ x} 1/p`, in the form of Dusart's statement. -/
noncomputable def primeRecip (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p

/-- Weights `log p` on primes, so that partial sums are `θ`. -/
noncomputable def cθ (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

/-- `f(t) = 1/(t log t)`. -/
noncomputable def fr (t : ℝ) : ℝ := 1 / (t * Real.log t)

/-- `w(t) = (log t + 1)/(t² log² t) = -f'(t)`. -/
noncomputable def w (t : ℝ) : ℝ := (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)

lemma sum_cθ (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cθ k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]; rfl

lemma hasDerivAt_fr {t : ℝ} (ht : 1 < t) : HasDerivAt fr (-w t) t := by
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have ht0 : t ≠ 0 := by linarith
  have h1 : HasDerivAt (fun t => t * Real.log t) (Real.log t + 1) t :=
    ((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht0)).congr_deriv (by field_simp)
  have h2 := h1.inv (mul_ne_zero ht0 hl)
  have hfr : fr = fun t => (t * Real.log t)⁻¹ := funext fun t => one_div _
  rw [hfr]
  exact h2.congr_deriv (by unfold w; field_simp)

lemma continuousOn_w {a b : ℝ} (ha : 1 < a) : ContinuousOn w (Set.Icc a b) := by
  intro t ht
  have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
  have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
  have ht0 : t ≠ 0 := by linarith
  have hc : ContinuousAt Real.log t := Real.continuousAt_log ht0
  apply ContinuousAt.continuousWithinAt
  unfold w
  exact ((hc.add continuousAt_const).div ((continuousAt_id.pow 2).mul (hc.pow 2))
    (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hl)))

/-- **Abel summation.** `∑_{p ≤ x} 1/p = θ(x)/(x log x) + ∫_{3/2}^x w(t) θ(t) dt` for `x ≥ 2`. -/
theorem abel_primeRecip {x : ℝ} (hx : 2 ≤ x) :
    primeRecip x = Chebyshev.theta x * fr x + ∫ t in Set.Ioc (3 / 2 : ℝ) x, w t * Chebyshev.theta t := by
  have hdiff : ∀ t ∈ Set.Icc (3 / 2 : ℝ) x, DifferentiableAt ℝ fr t := fun t ht =>
    (hasDerivAt_fr (by linarith [ht.1])).differentiableAt
  have hderiv : Set.EqOn (deriv fr) (fun t => -w t) (Set.Icc (3 / 2 : ℝ) x) := fun t ht =>
    (hasDerivAt_fr (by linarith [ht.1])).deriv
  have hint : IntegrableOn (deriv fr) (Set.Icc (3 / 2 : ℝ) x) :=
    ((continuousOn_w (by norm_num)).neg.integrableOn_Icc).congr_fun hderiv.symm measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul cθ (a := 3 / 2) (b := x) (by norm_num) (by linarith) hdiff hint
  have hfl : ⌊(3 / 2 : ℝ)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  rw [hfl, show ∑ k ∈ Finset.Icc 0 1, cθ k = 0 by
    simp [Finset.sum_Icc_succ_top, cθ, Nat.not_prime_zero, Nat.not_prime_one], mul_zero, sub_zero,
    sum_cθ] at h
  have hI : ∫ t in Set.Ioc (3 / 2 : ℝ) x, deriv fr t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cθ k =
      -∫ t in Set.Ioc (3 / 2 : ℝ) x, w t * Chebyshev.theta t := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [hderiv (Set.Ioc_subset_Icc_self ht), sum_cθ]; ring
  rw [hI] at h
  have hL : primeRecip x = ∑ k ∈ Finset.Ioc 1 ⌊x⌋₊, fr k * cθ k := by
    unfold primeRecip
    rw [Finset.sum_filter]
    symm
    have hsub : Finset.Ioc 1 ⌊x⌋₊ ⊆ Finset.range (⌊x⌋₊ + 1) := fun k hk => by
      simp only [Finset.mem_Ioc, Finset.mem_range] at hk ⊢; omega
    rw [Finset.sum_subset hsub ?_]
    · refine Finset.sum_congr rfl fun k _ => ?_
      unfold cθ fr
      split_ifs with hp
      · have hl : Real.log k ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
        have hk : (k : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        field_simp
      · simp
    · intro k hr hk
      simp only [Finset.mem_Ioc, not_and, not_le] at hk
      simp only [Finset.mem_range] at hr
      have : k ≤ 1 := by by_contra hc; have := hk (by omega); omega
      have hnp : ¬ k.Prime := fun hp => by have := hp.two_le; omega
      simp [cθ, hnp]
  rw [hL, h]; ring

/-- `t w(t)` has primitive `log log t - 1/log t` on `t > 1`. -/
lemma hasDerivAt_G {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => Real.log (Real.log t) - 1 / Real.log t) (t * w t) t := by
  have hlp : 0 < Real.log t := Real.log_pos ht
  have ht0 : t ≠ 0 := by linarith
  have hlog := Real.hasDerivAt_log ht0
  have h3 := (hlog.log hlp.ne').sub (hlog.inv hlp.ne')
  have hfun : (fun t => Real.log (Real.log t) - 1 / Real.log t) = fun t => Real.log (Real.log t) - (Real.log t)⁻¹ :=
    funext fun t => by rw [one_div]
  rw [hfun]
  exact h3.congr_deriv (by unfold w; field_simp; ring)

theorem integral_t_w {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, t * w t = (Real.log (Real.log x) - 1 / Real.log x) -
      (Real.log (Real.log 2) - 1 / Real.log 2) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_G ?_) ?_
  · rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
  · refine (ContinuousOn.intervalIntegrable ?_)
    rw [Set.uIcc_of_le hx]
    exact continuousOn_id.mul (continuousOn_w (by norm_num))

end Dusart
end

section

open Real MeasureTheory Set Filter Topology

set_option autoImplicit false

namespace Dusart

/-- `E(t) = θ(t) - t`. -/
noncomputable def E (t : ℝ) : ℝ := Chebyshev.theta t - t

lemma integrableOn_theta {a b : ℝ} : IntegrableOn Chebyshev.theta (Set.Icc a b) :=
  (Chebyshev.theta_mono.monotoneOn _).integrableOn_isCompact isCompact_Icc

lemma integrableOn_w_theta {a b : ℝ} (ha : 1 < a) :
    IntegrableOn (fun t => w t * Chebyshev.theta t) (Set.Icc a b) :=
  IntegrableOn.continuousOn_mul (continuousOn_w ha) integrableOn_theta isCompact_Icc

lemma integrableOn_w_E {a b : ℝ} (ha : 1 < a) : IntegrableOn (fun t => w t * E t) (Set.Icc a b) := by
  have h2 : IntegrableOn (fun t => w t * t) (Set.Icc a b) :=
    (ContinuousOn.mul (continuousOn_w ha) continuousOn_id).integrableOn_Icc
  refine ((integrableOn_w_theta ha).sub h2).congr_fun (fun t _ => ?_) measurableSet_Icc
  simp only [E, Pi.sub_apply]; ring

/-- **The main-term cancellation.** For `x ≥ 2`,
`∑_{p ≤ x} 1/p - log log x = (1/log 2 - log log 2) + E(x)/(x log x) + ∫_2^x w E`. -/
theorem primeRecip_sub_loglog {x : ℝ} (hx : 2 ≤ x) :
    primeRecip x - Real.log (Real.log x) =
      (1 / Real.log 2 - Real.log (Real.log 2)) + E x * fr x + ∫ t in (2 : ℝ)..x, w t * E t := by
  rw [abel_primeRecip hx, ← intervalIntegral.integral_of_le (by linarith)]
  have hii : ∀ a b : ℝ, 3 / 2 ≤ a → a ≤ b → IntervalIntegrable (fun t => w t * Chebyshev.theta t) volume a b :=
    fun a b ha hab => (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 (integrableOn_w_theta (by linarith))
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 2) (hii _ _ le_rfl (by norm_num)) (hii _ _ (by norm_num) hx)]
  have h0 : ∫ t in (3 / 2 : ℝ)..2, w t * Chebyshev.theta t = 0 := by
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards [volume.ae_ne (2 : ℝ)] with t ht hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    rw [Chebyshev.theta_eq_zero_of_lt_two (lt_of_le_of_ne hmem.2 ht), mul_zero]
  have hI1 : IntervalIntegrable (fun t => t * w t) volume 2 x :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hx]; exact continuousOn_id.mul (continuousOn_w (by norm_num)))
  have hI2 : IntervalIntegrable (fun t => w t * E t) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).2 (integrableOn_w_E (by norm_num))
  have hsplit : ∫ t in (2 : ℝ)..x, w t * Chebyshev.theta t =
      (∫ t in (2 : ℝ)..x, t * w t) + ∫ t in (2 : ℝ)..x, w t * E t := by
    rw [← intervalIntegral.integral_add hI1 hI2]
    exact intervalIntegral.integral_congr fun t _ => by simp only [E]; ring
  rw [h0, zero_add, hsplit]
  have hT := integral_t_w hx
  have hl : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hx0 : x ≠ 0 := by linarith
  have key : Chebyshev.theta x * fr x = 1 / Real.log x + E x * fr x := by
    simp only [E, fr]; field_simp; ring
  linarith [hT, key]

end Dusart
end

section

open Real MeasureTheory Set Filter Topology

set_option autoImplicit false

namespace Dusart

/-- `g(t) = (log t + 1)/(t log⁴ t) = (t / log² t) · w(t)`. -/
noncomputable def g (t : ℝ) : ℝ := (Real.log t + 1) / (t * Real.log t ^ 4)

lemma g_eq {t : ℝ} (ht : 1 < t) : t / Real.log t ^ 2 * w t = g t := by
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have ht0 : t ≠ 0 := by linarith
  simp only [w, g]; field_simp

lemma w_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ w t := by
  have := Real.log_pos ht; simp only [w]; positivity

lemma g_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ g t := by
  have := Real.log_pos ht; have : 0 < t := by linarith
  simp only [g]; positivity

/-- primitive of `g`: `-1/(2 log² t) - 1/(3 log³ t)`. -/
noncomputable def Gt (t : ℝ) : ℝ := -(1 / (2 * Real.log t ^ 2)) - 1 / (3 * Real.log t ^ 3)

lemma hasDerivAt_Gt {t : ℝ} (ht : 1 < t) : HasDerivAt Gt (g t) t := by
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have ht0 : t ≠ 0 := by linarith
  have hlog := Real.hasDerivAt_log ht0
  have h2 := ((hlog.pow 2).const_mul 2).inv (mul_ne_zero two_ne_zero (pow_ne_zero 2 hl))
  have h3 := ((hlog.pow 3).const_mul 3).inv (mul_ne_zero three_ne_zero (pow_ne_zero 3 hl))
  simp only [Pi.pow_apply] at h2 h3
  have hG : Gt = fun t => -(2 * Real.log t ^ 2)⁻¹ - (3 * Real.log t ^ 3)⁻¹ :=
    funext fun t => by simp only [Gt, one_div]
  rw [hG]
  exact (h2.neg.sub h3).congr_deriv (by simp only [g]; field_simp; ring)

lemma tendsto_Gt : Tendsto Gt atTop (𝓝 0) := by
  have h2 : Tendsto (fun t => 2 * Real.log t ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop |>.const_mul_atTop (by norm_num)
  have h3 : Tendsto (fun t => 3 * Real.log t ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop |>.const_mul_atTop (by norm_num)
  have := (h2.inv_tendsto_atTop.neg).sub h3.inv_tendsto_atTop
  simp only [neg_zero, sub_zero] at this
  refine this.congr fun t => ?_
  simp only [Gt, one_div, Pi.inv_apply]

lemma continuousWithinAt_Gt {x : ℝ} (hx : 1 < x) : ContinuousWithinAt Gt (Set.Ici x) x :=
  (hasDerivAt_Gt hx).continuousAt.continuousWithinAt

lemma integrableOn_g {x : ℝ} (hx : 1 < x) : IntegrableOn g (Set.Ioi x) :=
  integrableOn_Ioi_deriv_of_nonneg (continuousWithinAt_Gt hx)
    (fun t ht => hasDerivAt_Gt (lt_trans hx ht)) (fun t ht => g_nonneg (lt_trans hx ht)) tendsto_Gt

/-- `∫_x^∞ (t/log² t) w(t) dt = 1/(2 log² x) + 1/(3 log³ x)`. -/
theorem integral_g {x : ℝ} (hx : 1 < x) :
    ∫ t in Set.Ioi x, g t = 1 / (2 * Real.log x ^ 2) + 1 / (3 * Real.log x ^ 3) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (continuousWithinAt_Gt hx)
    (fun t ht => hasDerivAt_Gt (lt_trans hx ht)) (fun t ht => g_nonneg (lt_trans hx ht)) tendsto_Gt]
  simp only [Gt]; ring

lemma measurable_E : Measurable E :=
  Chebyshev.theta_mono.measurable.sub measurable_id

lemma measurable_w : Measurable w := by
  unfold w; fun_prop

/-- Integrability of `w E` on `(2, ∞)` from `|E(t)| ≤ C t / log² t` for `t ≥ T`. -/
theorem integrableOn_wE {T C : ℝ} (hT : 2 ≤ T)
    (hθ : ∀ t, T ≤ t → |E t| ≤ C * t / Real.log t ^ 2) :
    IntegrableOn (fun t => w t * E t) (Set.Ioi 2) := by
  have hI1 : IntegrableOn (fun t => w t * E t) (Set.Ioc 2 T) :=
    (integrableOn_w_E (a := 2) (b := T) (by norm_num)).mono_set Set.Ioc_subset_Icc_self
  have hI2 : IntegrableOn (fun t => w t * E t) (Set.Ioi T) := by
    refine Integrable.mono' ((integrableOn_g (by linarith : (1 : ℝ) < T)).const_mul C)
      ((measurable_w.mul measurable_E).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht1 : 1 < t := by linarith [show T < t from ht]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (w_nonneg ht1), ← g_eq ht1]
    have h := hθ t (le_of_lt ht)
    calc w t * |E t| ≤ w t * (C * t / Real.log t ^ 2) := mul_le_mul_of_nonneg_left h (w_nonneg ht1)
      _ = C * (t / Real.log t ^ 2 * w t) := by ring
  rw [← Set.Ioc_union_Ioi_eq_Ioi hT]
  exact hI1.union hI2

/-- The constant `M = 1/log 2 - log log 2 + ∫_2^∞ w E` (the limit of `∑_{p ≤ x} 1/p - log log x`). -/
noncomputable def Mconst : ℝ := 1 / Real.log 2 - Real.log (Real.log 2) + ∫ t in Set.Ioi 2, w t * E t

/-- **Tail identity.** `∑_{p ≤ x} 1/p - log log x - M = E(x)/(x log x) - ∫_x^∞ w E`. -/
theorem primeRecip_sub_M {x : ℝ} (hx : 2 ≤ x) (hint : IntegrableOn (fun t => w t * E t) (Set.Ioi 2)) :
    primeRecip x - Real.log (Real.log x) - Mconst = E x * fr x - ∫ t in Set.Ioi x, w t * E t := by
  rw [primeRecip_sub_loglog hx, Mconst, intervalIntegral.integral_of_le hx]
  have hsplit : ∫ t in Set.Ioi 2, w t * E t = (∫ t in Set.Ioc 2 x, w t * E t) + ∫ t in Set.Ioi x, w t * E t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set (Set.Ioc_subset_Ioi_self)) (hint.mono_set (Set.Ioi_subset_Ioi hx))
  rw [hsplit]; ring

/-- **Asymmetric transfer.** If `E(x) ≤ α x / log² x` and `E(t) ≥ -β t / log² t` for `t ≥ x`, then
`∑_{p ≤ x} 1/p - log log x - M ≤ β/(2 log² x) + (α + β/3)/log³ x`. -/
theorem transfer {x α β : ℝ} (hx : 2 ≤ x) (hβ : 0 ≤ β)
    (hint : IntegrableOn (fun t => w t * E t) (Set.Ioi 2))
    (hup : E x ≤ α * x / Real.log x ^ 2)
    (hlow : ∀ t, x ≤ t → -(β * t / Real.log t ^ 2) ≤ E t) :
    primeRecip x - Real.log (Real.log x) - Mconst ≤
      β / (2 * Real.log x ^ 2) + (α + β / 3) / Real.log x ^ 3 := by
  rw [primeRecip_sub_M hx hint]
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  have h1 : E x * fr x ≤ α / Real.log x ^ 3 := by
    have hfr : 0 < fr x := by simp only [fr]; positivity
    calc E x * fr x ≤ α * x / Real.log x ^ 2 * fr x := mul_le_mul_of_nonneg_right hup hfr.le
      _ = α / Real.log x ^ 3 := by simp only [fr]; field_simp
  have h2 : -∫ t in Set.Ioi x, w t * E t ≤ β * (1 / (2 * Real.log x ^ 2) + 1 / (3 * Real.log x ^ 3)) := by
    rw [← integral_g (by linarith), ← integral_const_mul, ← integral_neg]
    refine setIntegral_mono_on (hint.mono_set (Set.Ioi_subset_Ioi hx)).neg
      ((integrableOn_g (by linarith)).const_mul β) measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := by linarith [show x < t from ht]
    rw [← g_eq ht1]
    have h := mul_le_mul_of_nonneg_left (hlow t (le_of_lt ht)) (w_nonneg ht1)
    have h' : w t * -(β * t / Real.log t ^ 2) = -(β * (t / Real.log t ^ 2 * w t)) := by ring
    show -(w t * E t) ≤ β * (t / Real.log t ^ 2 * w t)
    linarith [h, h']
  have : β * (1 / (2 * Real.log x ^ 2) + 1 / (3 * Real.log x ^ 3)) + α / Real.log x ^ 3 =
      β / (2 * Real.log x ^ 2) + (α + β / 3) / Real.log x ^ 3 := by field_simp; ring
  linarith

/-- **Existence of the Mertens limit.** Under `|E(t)| ≤ C t / log² t` for `t ≥ T`,
`∑_{p ≤ x} 1/p - log log x → M`. -/
theorem tendsto_primeRecip {T C : ℝ} (hT : 2 ≤ T) (hC : 0 ≤ C)
    (hθ : ∀ t, T ≤ t → |E t| ≤ C * t / Real.log t ^ 2) :
    Tendsto (fun x => primeRecip x - Real.log (Real.log x)) atTop (𝓝 Mconst) := by
  have hint := integrableOn_wE hT hθ
  have h1 : Tendsto (fun x => E x * fr x) atTop (𝓝 0) := by
    have hb : Tendsto (fun x => C / Real.log x ^ 3) atTop (𝓝 0) :=
      ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop).const_div_atTop C
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop T] with x hx
    have hx1 : 1 < x := by linarith
    have hL : 0 < Real.log x := Real.log_pos hx1
    have hx0 : 0 < x := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by simp only [fr]; positivity : 0 < fr x)]
    calc |E x| * fr x ≤ C * x / Real.log x ^ 2 * fr x :=
          mul_le_mul_of_nonneg_right (hθ x hx) (by simp only [fr]; positivity)
      _ = C / Real.log x ^ 3 := by simp only [fr]; field_simp
  have h2 : Tendsto (fun x => ∫ t in (2 : ℝ)..x, w t * E t) atTop (𝓝 (∫ t in Set.Ioi 2, w t * E t)) :=
    intervalIntegral_tendsto_integral_Ioi 2 hint tendsto_id
  have h3 := (h1.add h2).const_add (1 / Real.log 2 - Real.log (Real.log 2))
  rw [zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [primeRecip_sub_loglog hx]; ring

end Dusart
end

section

open Real MeasureTheory Set Filter Topology

set_option autoImplicit false

namespace Dusart

/-- Mertens' constant `B = γ + ∑_p (log(1 - 1/p) + 1/p)`, as in Dusart's statement. -/
noncomputable def Bconst : ℝ :=
  Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))

/-- The right side of Dusart's Theorem 6.10. -/
noncomputable def dusartRhs (x : ℝ) : ℝ := 1 / (10 * Real.log x ^ 2) + 4 / (15 * Real.log x ^ 3)

/-- **Dusart's Theorem 6.10 from its three inputs.** (i) the θ estimate `|θ(t) - t| ≤ t/(5 log² t)` for
`t ≥ 3594641` (Dusart, Theorem 5.2); (ii) the identification of the Mertens limit with `B`; (iii) the bound on the
finite range `[10372, 3594641]`. Then the bound holds for every `x ≥ 10372`. -/
theorem dusart_of_inputs
    (hθ : ∀ t : ℝ, 3594641 ≤ t → |E t| ≤ (1 / 5) * t / Real.log t ^ 2)
    (hM : Mconst = Bconst)
    (hfin : ∀ x : ℝ, 10372 ≤ x → x ≤ 3594641 →
      primeRecip x - Real.log (Real.log x) - Bconst ≤ dusartRhs x)
    (x : ℝ) (hx : 10372 ≤ x) :
    primeRecip x - Real.log (Real.log x) - Bconst ≤ dusartRhs x := by
  rcases le_or_gt x 3594641 with h | h
  · exact hfin x hx h
  have hint := integrableOn_wE (by norm_num : (2 : ℝ) ≤ 3594641) hθ
  have hup : E x ≤ (1 / 5) * x / Real.log x ^ 2 := (le_abs_self _).trans (hθ x h.le)
  have hlow : ∀ t, x ≤ t → -((1 / 5) * t / Real.log t ^ 2) ≤ E t := fun t ht =>
    neg_le_of_abs_le (hθ t (by linarith))
  have := transfer (by linarith) (by norm_num) hint hup hlow
  rw [hM] at this
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  calc _ ≤ _ := this
    _ = dusartRhs x := by simp only [dusartRhs]; field_simp; ring

/-- The same statement in the exact form of the milestone. -/
theorem dusart_reciprocal_primes_of_inputs
    (hθ : ∀ t : ℝ, 3594641 ≤ t → |Chebyshev.theta t - t| ≤ (1 / 5) * t / Real.log t ^ 2)
    (hM : Mconst = Bconst)
    (hfin : ∀ x : ℝ, 10372 ≤ x → x ≤ 3594641 →
      primeRecip x - Real.log (Real.log x) - Bconst ≤ dusartRhs x)
    (x : ℝ) (hx : 10372 ≤ x) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (10 * Real.log x ^ 2) + 4 / (15 * Real.log x ^ 3) :=
  dusart_of_inputs hθ hM hfin x hx

end Dusart
end

section

open Finset

set_option autoImplicit false

namespace DusartCert

lemma gaps_pos : ∀ i < 48, 0 < gaps.getD i 0 := by decide +kernel

lemma res_next : ∀ i < 48, (res.getD i 0 + gaps.getD i 0) % 210 = res.getD ((i + 1) % 48) 0 := by decide +kernel

lemma gap_between : ∀ i < 48, ∀ t < 11, 0 < t → t < gaps.getD i 0 → Nat.gcd ((res.getD i 0 + t) % 210) 210 ≠ 1 := by
  decide +kernel

lemma gaps_le : ∀ i < 48, gaps.getD i 0 ≤ 10 := by decide +kernel

lemma prime_dvd_210 : ∀ k ≤ 210, k ∣ 210 → k.Prime → k ≤ 7 := by decide +kernel

/-- Integers strictly between consecutive wheel candidates are not primes above 7. -/
lemma not_prime_between {i n k : ℕ} (hi : i < 48) (hn : n % 210 = res.getD i 0) (hk1 : n < k)
    (hk2 : k < n + gaps.getD i 0) : ¬ (k.Prime ∧ 7 < k) := by
  rintro ⟨hp, h7⟩
  have hgl := gaps_le i hi
  have hg := gap_between i hi (k - n) (by omega) (by omega) (by omega)
  have hmod : (res.getD i 0 + (k - n)) % 210 = k % 210 := by
    rw [← hn]; omega
  rw [hmod, ← Nat.gcd_rec] at hg
  have hdvd : k ∣ 210 := by
    by_contra h
    exact hg (by rw [Nat.gcd_comm]; exact (hp.coprime_iff_not_dvd.2 h))
  have := prime_dvd_210 k (Nat.le_of_dvd (by norm_num) hdvd) hdvd hp
  omega

lemma one_div_le_ceil' {Q n : ℕ} (hQ : 0 < Q) (hn : 0 < n) :
    (1 : ℝ) / n ≤ (((Q + n - 1) / n : ℕ) : ℝ) / Q := by
  have h1 : Q ≤ (Q + n - 1) / n * n := by
    have h2 := Nat.div_add_mod (Q + n - 1) n
    have h3 := Nat.mod_lt (Q + n - 1) hn
    rw [Nat.mul_comm] at h2
    generalize (Q + n - 1) / n * n = X at *
    omega
  rw [div_le_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast hQ), one_mul]
  exact_mod_cast h1

lemma one_div_le_cdiv {Q D : ℕ} (hQ : 0 < Q) (hD : 0 < D) : (1 : ℝ) / D ≤ (cdiv Q D : ℝ) / Q :=
  one_div_le_ceil' hQ hD

/-- `g(n) = -log(1 - 1/n) - 1/n`. -/
noncomputable def gR (n : ℕ) : ℝ := -Real.log (1 - 1 / (n : ℝ)) - 1 / (n : ℝ)

lemma gpart_ge (Q n : ℕ) (hQ : 0 < Q) (hn : 0 < n) : ∀ m : ℕ,
    (∑ j ∈ Finset.range (m - 1), (1 / (n : ℝ)) ^ (j + 2) / ((j : ℝ) + 2)) ≤ (gpart Q n m : ℝ) / Q := by
  intro m
  induction m with
  | zero => simp [gpart]
  | succ m ih =>
    rcases m with _ | k
    · simp [gpart]
    · rw [show k + 1 + 1 - 1 = (k + 1 - 1) + 1 by omega, Finset.sum_range_succ,
        show gpart Q n (k + 1 + 1) = gpart Q n (k + 1) + cdiv Q ((k + 2) * n ^ (k + 2)) from rfl,
        Nat.cast_add, add_div]
      have hD : 0 < (k + 2) * n ^ (k + 2) := by positivity
      have hterm := one_div_le_cdiv (Q := Q) hQ hD
      have heq : (1 / (n : ℝ)) ^ (k + 1 - 1 + 2) / (((k + 1 - 1 : ℕ) : ℝ) + 2) = 1 / (((k + 2) * n ^ (k + 2) : ℕ) : ℝ) := by
        rw [show k + 1 - 1 = k by omega]
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        push_cast; rw [div_pow, one_pow]; field_simp
      rw [heq]; linarith

lemma gR_le (Q n : ℕ) (hQ : 0 < Q) (hn : 2 ≤ n) : gR n ≤ (wG Q n : ℝ) / Q := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hx0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hx1 : 1 / (n : ℝ) ≤ 1 / 2 := by gcongr
  have habs : |1 / (n : ℝ)| < 1 := by rw [abs_of_pos hx0]; linarith
  have hm4 : 4 ≤ gord n := by simp only [gord]; split_ifs <;> norm_num
  have hS := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hsplit := hS.summable.sum_add_tsum_nat_add (gord n)
  rw [hS.tsum_eq] at hsplit
  have hhead : ∑ j ∈ Finset.range (gord n), (1 / (n : ℝ)) ^ (j + 1) / ((j : ℝ) + 1) =
      1 / (n : ℝ) + ∑ j ∈ Finset.range (gord n - 1), (1 / (n : ℝ)) ^ (j + 2) / ((j : ℝ) + 2) := by
    rw [show gord n = (gord n - 1) + 1 by omega, Finset.sum_range_succ', add_comm]
    simp only [Nat.cast_add, Nat.cast_one, pow_one, zero_add, Nat.cast_zero, div_one]
    congr 1
    refine Finset.sum_congr (by congr 1) fun j _ => ?_
    ring_nf
  set m := gord n with hm
  have hgeo : Summable fun j : ℕ => (1 / (n : ℝ)) ^ (m + 1) / ((m : ℝ) + 1) * (1 / (n : ℝ)) ^ j :=
    (summable_geometric_of_lt_one hx0.le (by linarith)).mul_left _
  have hle : ∀ j : ℕ, (1 / (n : ℝ)) ^ (j + m + 1) / (((j + m : ℕ) : ℝ) + 1) ≤
      (1 / (n : ℝ)) ^ (m + 1) / ((m : ℝ) + 1) * (1 / (n : ℝ)) ^ j := by
    intro j
    have hpos : 0 < ((m : ℝ) + 1) := by positivity
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hpos, ← pow_add,
      show m + 1 + j = j + m + 1 by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    push_cast; linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
  have htail : ∑' j : ℕ, (1 / (n : ℝ)) ^ (j + m + 1) / (((j + m : ℕ) : ℝ) + 1) ≤
      1 / (((m + 1) * n ^ m * (n - 1) : ℕ) : ℝ) := by
    calc ∑' j : ℕ, (1 / (n : ℝ)) ^ (j + m + 1) / (((j + m : ℕ) : ℝ) + 1)
        ≤ ∑' j : ℕ, (1 / (n : ℝ)) ^ (m + 1) / ((m : ℝ) + 1) * (1 / (n : ℝ)) ^ j :=
          Summable.tsum_le_tsum hle (hgeo.of_nonneg_of_le (fun j => by positivity) hle) hgeo
      _ = (1 / (n : ℝ)) ^ (m + 1) / ((m : ℝ) + 1) * (1 - 1 / (n : ℝ))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hx0.le (by linarith)]
      _ = 1 / (((m + 1) * n ^ m * (n - 1) : ℕ) : ℝ) := by
          have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
          push_cast [hc]
          rw [div_pow, one_pow, pow_succ]
          field_simp
  have hD : 0 < (m + 1) * n ^ m * (n - 1) := by
    have : 0 < n - 1 := by omega
    positivity
  have h1 := one_div_le_cdiv (Q := Q) hQ hD
  have h2 := gpart_ge Q n hQ (by omega) m
  have hlog : -Real.log (1 - 1 / (n : ℝ)) = 1 / (n : ℝ) +
      ∑ j ∈ Finset.range (m - 1), (1 / (n : ℝ)) ^ (j + 2) / ((j : ℝ) + 2) +
      ∑' j : ℕ, (1 / (n : ℝ)) ^ (j + m + 1) / (((j + m : ℕ) : ℝ) + 1) := by
    rw [← hsplit, hhead]
  simp only [gR, wG, Nat.cast_add, add_div]
  rw [← hm, hlog]
  linarith [htail]

/-- **Soundness of the wheel checker.** -/
theorem step_sound (Q : ℕ) (hQ : 0 < Q) : ∀ (cs : List ℕ) (i n a b a' b' m : ℕ), i < 48 →
    n % 210 = res.getD i 0 → 2 ≤ n → step Q cs i n a b = some (a', b', m) →
    n ≤ m ∧ a ≤ a' ∧ b ≤ b' ∧
    (∑ p ∈ (Finset.Ico n m).filter (fun p => p.Prime ∧ 7 < p), (1 : ℝ) / p) ≤ ((a' - a : ℕ) : ℝ) / Q ∧
    (∑ p ∈ (Finset.Ico n m).filter (fun p => p.Prime ∧ 7 < p), gR p) ≤ ((b' - b : ℕ) : ℝ) / Q := by
  intro cs
  induction cs with
  | nil =>
    intro i n a b a' b' m _ _ _ h
    simp only [step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | cons c cs ih =>
    intro i n a b a' b' m hi hn hn2 h
    have hg := gaps_pos i hi
    have hi' : (i + 1) % 48 < 48 := Nat.mod_lt _ (by norm_num)
    have hn' : (n + gaps.getD i 0) % 210 = res.getD ((i + 1) % 48) 0 := by
      rw [← res_next i hi, Nat.add_mod, hn, Nat.add_mod (res.getD i 0)]; simp
    have hsplit : ∀ (F : ℕ → ℝ) (m' : ℕ), n + gaps.getD i 0 ≤ m' →
        (∑ p ∈ (Finset.Ico n m').filter (fun p => p.Prime ∧ 7 < p), F p) =
          (if n.Prime ∧ 7 < n then F n else 0) +
          ∑ p ∈ (Finset.Ico (n + gaps.getD i 0) m').filter (fun p => p.Prime ∧ 7 < p), F p := by
      intro F m' hm'
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_Ico_consecutive _ (by omega : n ≤ n + gaps.getD i 0) hm']
      congr 1
      rw [Finset.sum_eq_single_of_mem n (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩)]
      intro k hk hkn
      simp only [Finset.mem_Ico] at hk
      rw [if_neg (not_prime_between hi hn (by omega) hk.2)]
    have hcast : ∀ u v w : ℕ, u + w ≤ v → ((v - u : ℕ) : ℝ) = ((v - (u + w) : ℕ) : ℝ) + (w : ℝ) := by
      intro u v w h; rw [← Nat.cast_add]; congr 1; omega
    rw [step] at h
    split_ifs at h with hc hv
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ih _ _ _ _ _ _ _ hi' hn' (by omega) h
      refine ⟨by omega, le_trans (Nat.le_add_right _ _) h2, le_trans (Nat.le_add_right _ _) h3, ?_, ?_⟩
      · rw [hsplit _ m h1, hcast _ _ _ h2, add_div]
        have : (if n.Prime ∧ 7 < n then (1 : ℝ) / n else 0) ≤ (cdiv Q n : ℝ) / Q := by
          split_ifs
          · exact one_div_le_cdiv hQ (by omega)
          · positivity
        linarith
      · rw [hsplit _ m h1, hcast _ _ _ h3, add_div]
        have : (if n.Prime ∧ 7 < n then gR n else 0) ≤ (wG Q n : ℝ) / Q := by
          split_ifs
          · exact gR_le Q n hQ hn2
          · positivity
        linarith
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ih _ _ _ _ _ _ _ hi' hn' (by omega) h
      have hnp : ¬ (n.Prime ∧ 7 < n) := by
        rintro ⟨hp, _⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
        exact (Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hv.2) (by omega) hv.1.2) hp
      refine ⟨by omega, h2, h3, ?_, ?_⟩
      · rw [hsplit _ m h1, if_neg hnp, zero_add]; exact h4
      · rw [hsplit _ m h1, if_neg hnp, zero_add]; exact h5

end DusartCert
end

section

open Finset

set_option autoImplicit false

namespace DusartCert

/-- The atanh series for `log y`, `y ≥ 1`. -/
lemma hasSum_log_atanh {y : ℝ} (hy : 1 ≤ y) :
    HasSum (fun j : ℕ => 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1)) (Real.log y) := by
  have hz0 : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) (by linarith)
  have hz1 : (y - 1) / (y + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := (y - 1) / (y + 1)) (by rw [abs_of_nonneg hz0]; exact hz1)
  convert h using 1
  rw [← Real.log_div (by positivity) (by linarith)]
  congr 1
  field_simp; ring

lemma atanh_lower {y : ℝ} (hy : 1 ≤ y) (K : ℕ) :
    ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1) ≤ Real.log y := by
  have hz0 : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) (by linarith)
  exact sum_le_hasSum _ (fun j _ => by positivity) (hasSum_log_atanh hy)

lemma atanh_upper {y : ℝ} (hy : 1 ≤ y) (K : ℕ) :
    Real.log y ≤ ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1) +
      2 * ((y - 1) / (y + 1)) ^ (2 * K + 1) / ((2 * K + 1) * (1 - ((y - 1) / (y + 1)) ^ 2)) := by
  set z := (y - 1) / (y + 1) with hz
  have hz0 : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  have hS := hasSum_log_atanh hy
  rw [← hz] at hS
  have hsplit := hS.summable.sum_add_tsum_nat_add K
  rw [hS.tsum_eq] at hsplit
  rw [← hsplit]
  gcongr
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hgeo : Summable fun j : ℕ => 2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j :=
    (summable_geometric_of_lt_one (by positivity) hz2).mul_left _
  have hle : ∀ j : ℕ, 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * z ^ (2 * (j + K) + 1) ≤
      2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j := by
    intro j
    rw [← pow_mul, show 2 * (j + K) + 1 = (2 * K + 1) + 2 * j by ring, pow_add]
    have h1 : 1 / (2 * ((j + K : ℕ) : ℝ) + 1) ≤ 1 / (2 * (K : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); push_cast; linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
    have h2 : 0 ≤ z ^ (2 * K + 1) * z ^ (2 * j) := by positivity
    calc 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * (z ^ (2 * K + 1) * z ^ (2 * j))
        ≤ 2 * (1 / (2 * (K : ℝ) + 1)) * (z ^ (2 * K + 1) * z ^ (2 * j)) := by gcongr
      _ = 2 * z ^ (2 * K + 1) / (2 * K + 1) * z ^ (2 * j) := by ring
  calc ∑' j : ℕ, 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * z ^ (2 * (j + K) + 1)
      ≤ ∑' j : ℕ, 2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j :=
        Summable.tsum_le_tsum hle (hgeo.of_nonneg_of_le (fun j => by positivity) hle) hgeo
    _ = 2 * z ^ (2 * K + 1) / ((2 * K + 1) * (1 - z ^ 2)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hz2]
        have : (1 - z ^ 2) ≠ 0 := by linarith
        field_simp

lemma floor_div_le (N D : ℕ) (hD : 0 < D) : ((N / D : ℕ) : ℝ) ≤ (N : ℝ) / D := by
  rw [le_div_iff₀ (by exact_mod_cast hD)]; exact_mod_cast Nat.div_mul_le_self N D

lemma le_cdiv (N D : ℕ) (hD : 0 < D) : (N : ℝ) / D ≤ (cdiv N D : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hD)]
  have h2 := Nat.div_add_mod (N + D - 1) D
  have h3 := Nat.mod_lt (N + D - 1) hD
  have : N ≤ cdiv N D * D := by
    unfold cdiv; rw [Nat.mul_comm] at h2
    generalize (N + D - 1) / D * D = X at *; omega
  exact_mod_cast this

/-- The real term `Q · 2 (a/b)^(2j+1)/(2j+1)`. -/
lemma lterm_real (Q a b j : ℕ) (hb : 0 < b) :
    (Q : ℝ) * (2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1)) =
      ((2 * Q * a ^ (2 * j + 1) : ℕ) : ℝ) / (((2 * j + 1) * b ^ (2 * j + 1) : ℕ) : ℝ) := by
  have : (b : ℝ) ≠ 0 := by positivity
  push_cast; rw [div_pow]; field_simp

lemma lsumLo_le (Q a b : ℕ) (hb : 0 < b) : ∀ K, (lsumLo Q a b K : ℝ) ≤
    (Q : ℝ) * ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) := by
  intro K; induction K with
  | zero => simp [lsumLo]
  | succ K ih =>
    rw [lsumLo, Nat.cast_add, sum_range_succ, mul_add, lterm_real Q a b K hb]
    have := floor_div_le (2 * Q * a ^ (2 * K + 1)) ((2 * K + 1) * b ^ (2 * K + 1)) (by positivity)
    unfold ltermLo; linarith

lemma lsumHi_ge (Q a b : ℕ) (hb : 0 < b) : ∀ K,
    (Q : ℝ) * ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) ≤ (lsumHi Q a b K : ℝ) := by
  intro K; induction K with
  | zero => simp [lsumHi]
  | succ K ih =>
    rw [lsumHi, Nat.cast_add, sum_range_succ, mul_add, lterm_real Q a b K hb]
    have := le_cdiv (2 * Q * a ^ (2 * K + 1)) ((2 * K + 1) * b ^ (2 * K + 1)) (by positivity)
    unfold ltermHi; linarith

/-- **Reduced log bounds.** For `0 < den ≤ num`: `logRedLo ≤ Q log(num/den) ≤ logRedHi`. -/
theorem logRed_bounds (Q num den : ℕ) (hd : 0 < den) (hle : den ≤ num) :
    (logRedLo Q num den : ℝ) ≤ Q * Real.log ((num : ℝ) / den) ∧
      Q * Real.log ((num : ℝ) / den) ≤ (logRedHi Q num den : ℝ) := by
  have hden : (0 : ℝ) < den := by exact_mod_cast hd
  have hy : (1 : ℝ) ≤ (num : ℝ) / den := by rw [le_div_iff₀ hden]; simp; exact_mod_cast hle
  have hb : 0 < num + den := by omega
  have hz : ((num : ℝ) / den - 1) / ((num : ℝ) / den + 1) = (((num - den : ℕ) : ℝ)) / ((num + den : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle]; push_cast; field_simp
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  constructor
  · have := atanh_lower hy nterms
    rw [hz] at this
    exact (lsumLo_le Q (num - den) (num + den) hb nterms).trans (mul_le_mul_of_nonneg_left this hQ)
  · have hu := atanh_upper hy nterms
    rw [hz] at hu
    have h1 := lsumHi_ge Q (num - den) (num + den) hb nterms
    -- remainder
    set a := num - den; set b := num + den
    have hab : a < b := by omega
    have hb2 : 0 < b ^ 2 - a ^ 2 := by
      have : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
      omega
    have hrem := le_cdiv (2 * Q * a ^ (2 * nterms + 1) * b ^ 2) ((2 * nterms + 1) * b ^ (2 * nterms + 1) * (b ^ 2 - a ^ 2))
      (by positivity)
    have hremeq : (Q : ℝ) * (2 * ((a : ℝ) / b) ^ (2 * nterms + 1) / ((2 * nterms + 1) * (1 - ((a : ℝ) / b) ^ 2))) =
        ((2 * Q * a ^ (2 * nterms + 1) * b ^ 2 : ℕ) : ℝ) /
          (((2 * nterms + 1) * b ^ (2 * nterms + 1) * (b ^ 2 - a ^ 2) : ℕ) : ℝ) := by
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      have hsub : ((b ^ 2 - a ^ 2 : ℕ) : ℝ) = (b : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hne : (b : ℝ) ^ 2 - (a : ℝ) ^ 2 ≠ 0 := by
        rw [← hsub]; exact_mod_cast hb2.ne'
      push_cast [hsub]
      simp only [div_pow]
      field_simp
    unfold logRedHi lrem
    rw [Nat.cast_add]
    calc (Q : ℝ) * Real.log ((num : ℝ) / den) ≤ (Q : ℝ) * (∑ j ∈ range nterms,
          2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) +
          2 * ((a : ℝ) / b) ^ (2 * nterms + 1) / ((2 * nterms + 1) * (1 - ((a : ℝ) / b) ^ 2))) :=
          mul_le_mul_of_nonneg_left hu hQ
      _ ≤ _ := by rw [mul_add, hremeq]; linarith

/-- **Log bounds with range reduction.** -/
theorem log_bounds (Q num den k : ℕ) (h : redOK num den k = true) :
    (logLo Q num den k : ℝ) ≤ Q * Real.log ((num : ℝ) / den) ∧
      Q * Real.log ((num : ℝ) / den) ≤ (logHi Q num den k : ℝ) := by
  simp only [redOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, _⟩, hd⟩ := h
  have h2 := logRed_bounds Q 2 1 one_pos (by norm_num)
  have hk := logRed_bounds Q num (den * 2 ^ k) (by positivity) h1
  have hden : (0 : ℝ) < den := by exact_mod_cast hd
  have hsplit : Real.log ((num : ℝ) / den) = k * Real.log 2 + Real.log ((num : ℝ) / ((den * 2 ^ k : ℕ) : ℝ)) := by
    have hnum : (0 : ℝ) < num := by
      have : 0 < den * 2 ^ k := by positivity
      exact_mod_cast lt_of_lt_of_le this h1
    push_cast
    rw [Real.log_div hnum.ne' hden.ne', Real.log_div hnum.ne' (by positivity : (den : ℝ) * 2 ^ k ≠ 0),
      Real.log_mul hden.ne' (by positivity), Real.log_pow]; ring
  have hl2 : Real.log ((2 : ℕ) / ((1 : ℕ) : ℝ)) = Real.log 2 := by norm_num
  rw [hl2] at h2
  unfold logLo logHi
  push_cast
  rw [hsplit]
  constructor
  · nlinarith [h2.1, hk.1, show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  · nlinarith [h2.2, hk.2, show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

end DusartCert
end

section

open Finset Filter Topology

set_option autoImplicit false

namespace DusartCert

lemma hsum_le (Q : ℕ) (hQ : 0 < Q) : ∀ n, (hsum Q n : ℝ) ≤ Q * (harmonic n : ℝ) := by
  intro n; induction n with
  | zero => simp [hsum]
  | succ n ih =>
    rw [hsum, harmonic_succ]; push_cast
    have := floor_div_le Q (n + 1) (by omega)
    have h : (Q : ℝ) / ((n + 1 : ℕ) : ℝ) = Q * (1 / ((n : ℝ) + 1)) := by push_cast; ring
    rw [h] at this; push_cast at this
    rw [mul_add]; rw [one_div] at this; linarith

/-- `log(1 + 1/n) ≤ 1/(2n) + 1/(2(n+1))`. -/
lemma log_succ_div_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (((n : ℝ) + 1) / n) ≤ 1 / (2 * n) + 1 / (2 * ((n : ℝ) + 1)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : (1 : ℝ) ≤ ((n : ℝ) + 1) / n := by rw [le_div_iff₀ (by linarith)]; linarith
  have h := atanh_upper hy 0
  simp only [range_zero, sum_empty, zero_add, mul_zero, pow_one, Nat.cast_zero] at h
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hz : (((n : ℝ) + 1) / n - 1) / (((n : ℝ) + 1) / n + 1) = 1 / (2 * (n : ℝ) + 1) := by
    field_simp; ring
  rw [hz] at h
  refine h.trans (le_of_eq ?_)
  have h2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h3 : (n : ℝ) + 1 ≠ 0 := by positivity
  have key : 1 - (1 / (2 * (n : ℝ) + 1)) ^ 2 = 4 * (n : ℝ) * ((n : ℝ) + 1) / (2 * (n : ℝ) + 1) ^ 2 := by
    field_simp; ring
  rw [key]
  field_simp; ring

/-- `H_n - log n - 1/(2n) ≤ γ` for `n ≥ 1`. -/
theorem gamma_ge {n : ℕ} (hn : 1 ≤ n) :
    (harmonic n : ℝ) - Real.log n - 1 / (2 * n) ≤ Real.eulerMascheroniConstant := by
  set a : ℕ → ℝ := fun k => Real.eulerMascheroniSeq' (k + 1) - 1 / (2 * ((k : ℝ) + 1))
  have hmono : Monotone a := by
    refine monotone_nat_of_le_succ fun k => ?_
    simp only [a, Real.eulerMascheroniSeq', Nat.add_one_ne_zero, if_false]
    have h := log_succ_div_le (n := k + 1) (by omega)
    rw [Real.log_div (by positivity) (by positivity)] at h
    have hH : (harmonic (k + 1 + 1) : ℝ) = harmonic (k + 1) + 1 / ((k : ℝ) + 2) := by
      rw [harmonic_succ]; push_cast; ring
    push_cast at h ⊢
    rw [hH]
    have e : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    rw [e] at h ⊢
    have e2 : 1 / ((k : ℝ) + 2) = 2 * (1 / (2 * ((k : ℝ) + 2))) := by field_simp
    linarith

  have hlim : Tendsto a atTop (𝓝 Real.eulerMascheroniConstant) := by
    have h1 := (Real.tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1))
    have h2 : Tendsto (fun k : ℕ => 1 / (2 * ((k : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).mul_const (1 / 2 : ℝ)
      rw [zero_mul] at this
      exact this.congr fun k => by field_simp
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    exact h3.congr fun k => rfl
  have := hmono.ge_of_tendsto hlim (n - 1)
  simp only [a, Real.eulerMascheroniSeq', Nat.add_one_ne_zero, if_false, Nat.sub_add_cancel hn] at this
  rw [show ((n - 1 : ℕ) : ℝ) + 1 = n by rw [Nat.cast_sub hn]; push_cast; ring] at this
  exact this

/-- `γ ≥ (hsum Q 1024 - 10 logRedHi Q 2 1)/Q - 1/2048`. -/
theorem gamma_lower (Q : ℕ) (hQ : 0 < Q) :
    (hsum Q 1024 : ℝ) / Q - 10 * ((logRedHi Q 2 1 : ℕ) : ℝ) / Q - 1 / 2048 ≤ Real.eulerMascheroniConstant := by
  have hg := gamma_ge (n := 1024) (by norm_num)
  have hH := hsum_le Q hQ 1024
  have hl := (logRed_bounds Q 2 1 one_pos (by norm_num)).2
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlog : Real.log ((1024 : ℕ) : ℝ) = 10 * Real.log 2 := by
    rw [show ((1024 : ℕ) : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have hl' : Real.log ((2 : ℕ) / ((1 : ℕ) : ℝ)) = Real.log 2 := by norm_num
  rw [hl'] at hl
  rw [hlog] at hg
  have e1 : (hsum Q 1024 : ℝ) / Q ≤ (harmonic 1024 : ℝ) := by rw [div_le_iff₀ hQ']; linarith
  have e2 : 10 * Real.log 2 ≤ 10 * ((logRedHi Q 2 1 : ℕ) : ℝ) / Q := by
    rw [le_div_iff₀ hQ']; nlinarith
  push_cast at hg ⊢
  linarith

lemma gR_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ gR n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - 1 / n by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by gcongr
    linarith)
  simp only [gR]; linarith

/-- `g(n) ≤ 1/(2n(n-1))`. -/
lemma gR_le_tail {n : ℕ} (hn : 2 ≤ n) : gR n ≤ 1 / (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hx1 : 1 / (n : ℝ) ≤ 1 / 2 := by gcongr
  have hS := Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / (n : ℝ)) (by rw [abs_of_pos hx0]; linarith)
  have hsplit := hS.summable.sum_add_tsum_nat_add 1
  rw [hS.tsum_eq] at hsplit
  set x := 1 / (n : ℝ) with hx
  have hgeo : Summable fun j : ℕ => x ^ 2 / 2 * x ^ j := (summable_geometric_of_lt_one hx0.le (by linarith)).mul_left _
  have hle : ∀ j : ℕ, x ^ (j + 1 + 1) / (((j + 1 : ℕ) : ℝ) + 1) ≤ x ^ 2 / 2 * x ^ j := by
    intro j
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num), ← pow_add,
      show 2 + j = j + 1 + 1 by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    push_cast; linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
  have htail : ∑' j : ℕ, x ^ (j + 1 + 1) / (((j + 1 : ℕ) : ℝ) + 1) ≤ x ^ 2 / (2 * (1 - x)) := by
    calc _ ≤ ∑' j : ℕ, x ^ 2 / 2 * x ^ j := Summable.tsum_le_tsum hle (hgeo.of_nonneg_of_le (fun j => by positivity) hle) hgeo
      _ = x ^ 2 / (2 * (1 - x)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hx0.le (by linarith)]
        have : 1 - x ≠ 0 := by linarith
        field_simp
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one] at hsplit
  simp only [gR]
  rw [← hx, ← hsplit]
  have : x ^ 2 / (2 * (1 - x)) = 1 / (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
    rw [hx]; have : (n : ℝ) - 1 ≠ 0 := by linarith
    have : (n : ℝ) ≠ 0 := by linarith
    field_simp
  linarith

/-- Telescoping: `∑_{n ∈ [E, N)} 1/(2n(n-1)) ≤ 1/(2(E-1))`. -/
lemma tele_le {E : ℕ} (hE : 2 ≤ E) : ∀ N, ∑ n ∈ Finset.Ico E N, 1 / (2 * (n : ℝ) * ((n : ℝ) - 1)) ≤ 1 / (2 * ((E : ℝ) - 1)) := by
  have hE' : (2 : ℝ) ≤ E := by exact_mod_cast hE
  suffices h : ∀ N, E ≤ N → ∑ n ∈ Finset.Ico E N, 1 / (2 * (n : ℝ) * ((n : ℝ) - 1)) =
      1 / (2 * ((E : ℝ) - 1)) - 1 / (2 * ((N : ℝ) - 1)) by
    intro N
    rcases le_or_gt E N with hN | hN
    · rw [h N hN]
      have hN' : (2 : ℝ) ≤ N := by exact_mod_cast le_trans hE hN
      have : 0 ≤ 1 / (2 * ((N : ℝ) - 1)) := by apply div_nonneg <;> linarith
      linarith
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; apply div_nonneg <;> linarith
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, ih]
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast le_trans hE hN
    push_cast
    rw [show (N : ℝ) + 1 - 1 = N by ring]
    have : (N : ℝ) - 1 ≠ 0 := by linarith
    have : (N : ℝ) ≠ 0 := by linarith
    have : (E : ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring

lemma small_primes : ∀ m ≤ 7, m.Prime → m = 2 ∨ m = 3 ∨ m = 5 ∨ m = 7 := by decide

lemma no_primes_8_10 : ∀ n, 8 ≤ n → n < 11 → ¬ n.Prime := by decide

/-- **Lower bound for Mertens' constant `B`.** -/
theorem B_lower (Q : ℕ) (hQ : 0 < Q) {E Gmid : ℕ} (hE : 12 ≤ E)
    (hG : (∑ p ∈ (Finset.Ico 11 E).filter (fun p => p.Prime ∧ 7 < p), gR p) ≤ (Gmid : ℝ) / Q) :
    Real.eulerMascheroniConstant - (wG Q 2 + wG Q 3 + wG Q 5 + wG Q 7 : ℕ) / (Q : ℝ) - (Gmid : ℝ) / Q -
        1 / (2 * ((E : ℝ) - 1)) ≤
      Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
  have hneg : ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) = -∑' p : Nat.Primes, gR p := by
    rw [← tsum_neg]; exact tsum_congr fun p => by simp [gR]; ring
  rw [hneg]
  have hsmall : gR 2 + gR 3 + gR 5 + gR 7 ≤ ((wG Q 2 + wG Q 3 + wG Q 5 + wG Q 7 : ℕ) : ℝ) / Q := by
    push_cast; rw [add_div, add_div, add_div]
    linarith [gR_le Q 2 hQ le_rfl, gR_le Q 3 hQ (by norm_num), gR_le Q 5 hQ (by norm_num), gR_le Q 7 hQ (by norm_num)]
  have hbound : ∑' p : Nat.Primes, gR p ≤
      (gR 2 + gR 3 + gR 5 + gR 7) + (Gmid : ℝ) / Q + 1 / (2 * ((E : ℝ) - 1)) := by
    refine tsum_le_of_sum_le' (by
      have := gR_nonneg (n := 2) le_rfl; have := gR_nonneg (n := 3) (by norm_num)
      have := gR_nonneg (n := 5) (by norm_num); have := gR_nonneg (n := 7) (by norm_num)
      have : (0 : ℝ) ≤ (Gmid : ℝ) / Q := by positivity
      have : (0 : ℝ) ≤ 1 / (2 * ((E : ℝ) - 1)) := by
        have : (12 : ℝ) ≤ E := by exact_mod_cast hE
        apply div_nonneg <;> linarith
      linarith) fun s => ?_
    -- map to ℕ
    set t : Finset ℕ := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hts : ∑ p ∈ s, gR p = ∑ n ∈ t, gR n := by
      exact (Finset.sum_map s ⟨Subtype.val, Subtype.val_injective⟩ gR).symm
    have htp : ∀ n ∈ t, n.Prime := by
      intro n hn
      obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 hn; exact p.prop
    rw [hts, ← Finset.sum_filter_add_sum_filter_not t (fun n => n < E)]
    have h1 : ∑ n ∈ t.filter (fun n => n < E), gR n ≤
        (gR 2 + gR 3 + gR 5 + gR 7) + ∑ p ∈ (Finset.Ico 11 E).filter (fun p => p.Prime ∧ 7 < p), gR p := by
      have hsub : t.filter (fun n => n < E) ⊆ {2, 3, 5, 7} ∪ (Finset.Ico 11 E).filter (fun p => p.Prime ∧ 7 < p) := by
        intro n hn
        simp only [Finset.mem_filter] at hn
        have hp := htp n hn.1
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_Ico]
        by_cases h7 : 7 < n
        · right
          have : 11 ≤ n := by
            by_contra h; exact no_primes_8_10 n (by omega) (by omega) hp
          exact ⟨⟨this, hn.2⟩, hp, h7⟩
        · left
          rcases small_primes n (by omega) hp with h | h | h | h <;> simp [h]
      calc ∑ n ∈ t.filter (fun n => n < E), gR n
          ≤ ∑ n ∈ {2, 3, 5, 7} ∪ (Finset.Ico 11 E).filter (fun p => p.Prime ∧ 7 < p), gR n := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => ?_
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
              Finset.mem_Ico] at hn
            exact gR_nonneg (by rcases hn with h | h <;> omega)
        _ ≤ _ := by
            rw [Finset.sum_union (by
              rw [Finset.disjoint_left]; intro n hn hn'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hn
              simp only [Finset.mem_filter, Finset.mem_Ico] at hn'; omega)]
            simp [add_assoc]
    have h2 : ∑ n ∈ t.filter (fun n => ¬ n < E), gR n ≤ 1 / (2 * ((E : ℝ) - 1)) := by
      calc ∑ n ∈ t.filter (fun n => ¬ n < E), gR n
          ≤ ∑ n ∈ t.filter (fun n => ¬ n < E), 1 / (2 * (n : ℝ) * ((n : ℝ) - 1)) :=
            Finset.sum_le_sum fun n hn => by
              simp only [Finset.mem_filter] at hn; exact gR_le_tail (by omega)
        _ ≤ ∑ n ∈ Finset.Ico E (t.sup id + 1), 1 / (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n hn _ => ?_
            · simp only [Finset.mem_filter] at hn
              simp only [Finset.mem_Ico]
              exact ⟨by omega, Nat.lt_succ_of_le (Finset.le_sup (f := id) hn.1)⟩
            · simp only [Finset.mem_Ico] at hn
              have : (12 : ℝ) ≤ n := by exact_mod_cast le_trans hE hn.1
              apply div_nonneg zero_le_one; nlinarith
        _ ≤ _ := tele_le (by omega) _
    linarith [h1, h2, hG]
  linarith [hsmall, hbound]

end DusartCert
end

section

open Finset

set_option autoImplicit false

namespace DusartCert

lemma step_end_index (Q : ℕ) : ∀ (cs : List ℕ) (i n a b a' b' m : ℕ), i < 48 → n % 210 = res.getD i 0 →
    step Q cs i n a b = some (a', b', m) → m % 210 = res.getD ((i + cs.length) % 48) 0 := by
  intro cs
  induction cs with
  | nil =>
    intro i n a b a' b' m hi hn h
    simp only [step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simpa [Nat.mod_eq_of_lt hi] using hn
  | cons c cs ih =>
    intro i n a b a' b' m hi hn h
    have hi' : (i + 1) % 48 < 48 := Nat.mod_lt _ (by norm_num)
    have hn' : (n + gaps.getD i 0) % 210 = res.getD ((i + 1) % 48) 0 := by
      rw [← res_next i hi, Nat.add_mod, hn, Nat.add_mod (res.getD i 0)]; simp
    have hidx : (i + (c :: cs).length) % 48 = ((i + 1) % 48 + cs.length) % 48 := by
      simp only [List.length_cons]; omega
    rw [hidx]
    rw [step] at h
    split_ifs at h
    · exact ih _ _ _ _ _ _ _ hi' hn' h
    · exact ih _ _ _ _ _ _ _ hi' hn' h

/-- The invariant of a run state. -/
def Inv (Q n i A G : ℕ) : Prop :=
  i < 48 ∧ n % 210 = res.getD i 0 ∧ 11 ≤ n ∧
    (∑ p ∈ (Finset.Ico 11 n).filter (fun p => p.Prime ∧ 7 < p), (1 : ℝ) / p) ≤ (A : ℝ) / Q ∧
    (∑ p ∈ (Finset.Ico 11 n).filter (fun p => p.Prime ∧ 7 < p), gR p) ≤ (G : ℝ) / Q

lemma Inv_start (Q : ℕ) : Inv Q 11 1 0 0 := by
  refine ⟨by norm_num, by decide, le_rfl, ?_, ?_⟩ <;> simp

lemma sum_Ico_split (F : ℕ → ℝ) {n n' : ℕ} (h1 : 11 ≤ n) (h2 : n ≤ n') :
    ∑ p ∈ (Finset.Ico 11 n').filter (fun p => p.Prime ∧ 7 < p), F p =
      ∑ p ∈ (Finset.Ico 11 n).filter (fun p => p.Prime ∧ 7 < p), F p +
      ∑ p ∈ (Finset.Ico n n').filter (fun p => p.Prime ∧ 7 < p), F p := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_Ico_consecutive _ h1 h2]

lemma primes_below (F : ℕ → ℝ) {N : ℕ} (hN : 11 ≤ N) :
    ∑ p ∈ (Finset.range N).filter Nat.Prime, F p =
      F 2 + F 3 + F 5 + F 7 + ∑ p ∈ (Finset.Ico 11 N).filter (fun p => p.Prime ∧ 7 < p), F p := by
  have hset : (Finset.range N).filter Nat.Prime = {2, 3, 5, 7} ∪ (Finset.Ico 11 N).filter (fun p => p.Prime ∧ 7 < p) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_Ico]
    constructor
    · rintro ⟨hn, hp⟩
      by_cases h7 : 7 < n
      · right
        have : 11 ≤ n := by by_contra h; exact no_primes_8_10 n (by omega) (by omega) hp
        exact ⟨⟨this, hn⟩, hp, h7⟩
      · left; rcases small_primes n (by omega) hp with h | h | h | h <;> simp [h]
    · rintro (h | ⟨⟨h1, h2⟩, hp, _⟩)
      · rcases h with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by norm_num⟩
      · exact ⟨h2, hp⟩
  rw [hset, Finset.sum_union (by
    rw [Finset.disjoint_left]; intro n hn hn'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn'; omega)]
  simp [add_assoc]

/-- The prime sum up to `x < N` is at most `(smallQ + A)/Q`. -/
lemma primeRecip_le {Q N A : ℕ} (hQ : 0 < Q) (hN : 11 ≤ N)
    (hA : (∑ p ∈ (Finset.Ico 11 N).filter (fun p => p.Prime ∧ 7 < p), (1 : ℝ) / p) ≤ (A : ℝ) / Q)
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x < N) : Dusart.primeRecip x ≤ ((smallQ Q + A : ℕ) : ℝ) / Q := by
  unfold Dusart.primeRecip
  have hsub : (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime ⊆ (Finset.range N).filter Nat.Prime := by
    refine Finset.filter_subset_filter _ (Finset.range_subset_range.2 ?_)
    have := (Nat.floor_lt hx0).2 (by exact_mod_cast hx); omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans ?_
  rw [primes_below (fun p => (1 : ℝ) / p) hN]
  have h2 := one_div_le_cdiv (Q := Q) (D := 2) hQ (by norm_num)
  have h3 := one_div_le_cdiv (Q := Q) (D := 3) hQ (by norm_num)
  have h5 := one_div_le_cdiv (Q := Q) (D := 5) hQ (by norm_num)
  have h7 := one_div_le_cdiv (Q := Q) (D := 7) hQ (by norm_num)
  simp only [smallQ]; push_cast at h2 h3 h5 h7 ⊢
  rw [add_div, add_div, add_div, add_div]
  linarith

/-- **Soundness of a cell check.** -/
theorem cell_sound {Q Blo a b Shi k1a k1b k2 : ℕ} (hQ : 0 < Q) (hc : cellOK Q Blo a b Shi k1a k1b k2 = true)
    (hS : ∀ x : ℝ, (a : ℝ) ≤ x → x < b → Dusart.primeRecip x ≤ (Shi : ℝ) / Q)
    (hB : (Blo : ℝ) / Q ≤ Dusart.Bconst) :
    ∀ x : ℝ, (a : ℝ) ≤ x → x < b →
      Dusart.primeRecip x - Real.log (Real.log x) - Dusart.Bconst ≤ Dusart.dusartRhs x := by
  intro x hax hxb
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hab, ha⟩, hb⟩, hL⟩, hmain⟩ := hc
  set Llo := logLo Q a 1 k1a
  set Lhi := logHi Q b 1 k1b
  set LL := logLo Q Llo Q k2
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hla := (log_bounds Q a 1 k1a ha).1
  have hlb := (log_bounds Q b 1 k1b hb).2
  have hll := (log_bounds Q Llo Q k2 hL).1
  simp only [Nat.cast_one, div_one] at hla hlb
  simp only [redOK, Bool.and_eq_true, decide_eq_true_eq] at ha hL
  have ha1 : (1 : ℝ) ≤ a := by
    have : 1 ≤ a := le_trans (Nat.one_le_two_pow) (by simpa using ha.1.1)
    exact_mod_cast this
  have hx0 : 0 < x := by linarith
  have hLlo : (Q : ℝ) ≤ Llo := by
    have : Q ≤ Llo := le_trans (Nat.le_mul_of_pos_right Q (Nat.two_pow_pos k2)) hL.1.1
    exact_mod_cast this
  -- log x bounds
  have hlogx : (Llo : ℝ) / Q ≤ Real.log x := by
    rw [div_le_iff₀ hQ']
    calc (Llo : ℝ) ≤ Q * Real.log a := hla
      _ ≤ Q * Real.log x := mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hax) hQ'.le
      _ = Real.log x * Q := by ring
  have hLQ : (1 : ℝ) ≤ (Llo : ℝ) / Q := by rw [le_div_iff₀ hQ']; linarith
  have hlogx1 : 1 ≤ Real.log x := le_trans hLQ hlogx
  have hlogxb : Q * Real.log x ≤ (Lhi : ℝ) := by
    calc (Q : ℝ) * Real.log x ≤ Q * Real.log b :=
          mul_le_mul_of_nonneg_left (Real.log_le_log hx0 hxb.le) hQ'.le
      _ ≤ Lhi := hlb
  -- log log x
  have hloglog : (LL : ℝ) / Q ≤ Real.log (Real.log x) := by
    rw [div_le_iff₀ hQ']
    calc (LL : ℝ) ≤ Q * Real.log ((Llo : ℝ) / Q) := hll
      _ ≤ Q * Real.log (Real.log x) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hlogx) hQ'.le
      _ = Real.log (Real.log x) * Q := by ring
  -- the right side
  have hLhipos : (0 : ℝ) < Lhi := by nlinarith
  have hr1 : ((Q ^ 3 / (10 * Lhi ^ 2) : ℕ) : ℝ) / Q ≤ 1 / (10 * Real.log x ^ 2) := by
    have hLn : 0 < Lhi := by exact_mod_cast hLhipos
    have hfl := floor_div_le (Q ^ 3) (10 * Lhi ^ 2) (Nat.mul_pos (by norm_num) (pow_pos hLn 2))
    rw [div_le_iff₀ hQ']
    refine hfl.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hl : Real.log x ≤ (Lhi : ℝ) / Q := by rw [le_div_iff₀ hQ']; linarith
    have hl2 : Real.log x ^ 2 ≤ ((Lhi : ℝ) / Q) ^ 2 := pow_le_pow_left₀ (by linarith) hl 2
    have hpos : 0 < Real.log x ^ 2 := by positivity
    rw [div_pow] at hl2
    rw [le_div_iff₀ (by positivity)] at hl2
    push_cast
    field_simp
    nlinarith
  have hr2 : ((4 * Q ^ 4 / (15 * Lhi ^ 3) : ℕ) : ℝ) / Q ≤ 4 / (15 * Real.log x ^ 3) := by
    have hLn : 0 < Lhi := by exact_mod_cast hLhipos
    have hfl := floor_div_le (4 * Q ^ 4) (15 * Lhi ^ 3) (Nat.mul_pos (by norm_num) (pow_pos hLn 3))
    rw [div_le_iff₀ hQ']
    refine hfl.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hl : Real.log x ≤ (Lhi : ℝ) / Q := by rw [le_div_iff₀ hQ']; linarith
    have hl3 : Real.log x ^ 3 ≤ ((Lhi : ℝ) / Q) ^ 3 := pow_le_pow_left₀ (by linarith) hl 3
    have hpos : 0 < Real.log x ^ 3 := by positivity
    rw [div_pow] at hl3
    rw [le_div_iff₀ (by positivity)] at hl3
    push_cast
    field_simp
    nlinarith
  have hS' := hS x hax hxb
  have hmain' : (Shi : ℝ) ≤ LL + ((Q ^ 3 / (10 * Lhi ^ 2) : ℕ) : ℝ) + ((4 * Q ^ 4 / (15 * Lhi ^ 3) : ℕ) : ℝ) + Blo := by
    exact_mod_cast (by simpa [add_assoc] using hmain)
  unfold Dusart.dusartRhs
  have e : (Shi : ℝ) / Q ≤ (LL : ℝ) / Q + ((Q ^ 3 / (10 * Lhi ^ 2) : ℕ) : ℝ) / Q +
      ((4 * Q ^ 4 / (15 * Lhi ^ 3) : ℕ) : ℝ) / Q + (Blo : ℝ) / Q := by
    rw [← add_div, ← add_div, ← add_div]; exact div_le_div_of_nonneg_right hmain' hQ'.le
  linarith

/-- **Soundness of a run.** -/
theorem run_sound (Q Blo : ℕ) (hQ : 0 < Q) (hB : (Blo : ℝ) / Q ≤ Dusart.Bconst) :
    ∀ (items : List (List ℕ × Option (ℕ × ℕ × ℕ))) (n i A G lb n2 i2 A2 G2 lb2 : ℕ),
      run Q Blo items (n, i, A, G, lb) = some (n2, i2, A2, G2, lb2) → Inv Q n i A G →
      Inv Q n2 i2 A2 G2 ∧ lb ≤ lb2 ∧
      ∀ x : ℝ, (lb : ℝ) ≤ x → x < lb2 →
        Dusart.primeRecip x - Real.log (Real.log x) - Dusart.Bconst ≤ Dusart.dusartRhs x := by
  intro items
  induction items with
  | nil =>
    intro n i A G lb n2 i2 A2 G2 lb2 h hI
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hI, le_rfl, fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)⟩
  | cons item rest ih =>
    intro n i A G lb n2 i2 A2 G2 lb2 h hI
    obtain ⟨codes, chk⟩ := item
    obtain ⟨hi, hn, h11, hA, hG⟩ := hI
    rw [run] at h
    rcases hst : step Q codes i n 0 0 with _ | ⟨a', g', n'⟩
    · rw [hst] at h; exact absurd h (by simp)
    rw [hst] at h
    obtain ⟨hnn', -, -, hA', hG'⟩ := step_sound Q hQ codes i n 0 0 a' g' n' hi hn (by omega) hst
    have hidx := step_end_index Q codes i n 0 0 a' g' n' hi hn hst
    have hI' : Inv Q n' ((i + codes.length) % 48) (A + a') (G + g') := by
      refine ⟨Nat.mod_lt _ (by norm_num), hidx, by omega, ?_, ?_⟩
      · rw [sum_Ico_split _ h11 hnn']; push_cast; rw [add_div]; rw [Nat.sub_zero] at hA'; linarith
      · rw [sum_Ico_split _ h11 hnn']; push_cast; rw [add_div]; rw [Nat.sub_zero] at hG'; linarith
    rcases chk with _ | ⟨k1a, k1b, k2⟩
    · obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ _ _ _ _ _ _ h hI'
      exact ⟨h1, h2, h3⟩
    · simp only at h
      split_ifs at h with hc
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ _ _ _ _ _ _ h hI'
      have hcell := cell_sound hQ hc (fun x hx1 hx2 => primeRecip_le hQ (by omega) hI'.2.2.2.1
        (by
          have : (1 : ℝ) ≤ lb := by
            simp only [cellOK, redOK, Bool.and_eq_true, decide_eq_true_eq] at hc
            exact_mod_cast le_trans Nat.one_le_two_pow (by simpa using hc.1.1.1.2.1.1)
          linarith) hx2) hB
      have hlbn : lb ≤ n' := by
        simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1.1.1.1
      refine ⟨h1, by omega, fun x hx1 hx2 => ?_⟩
      rcases lt_or_ge x n' with hx | hx
      · exact hcell x hx1 hx
      · exact h3 x (by exact_mod_cast hx) hx2

/-- **The B bound from the final state.** -/
theorem B_from_bOK {Q Blo E G : ℕ} (hQ : 0 < Q) (hb : bOK Q Blo E G = true)
    (hG : (∑ p ∈ (Finset.Ico 11 E).filter (fun p => p.Prime ∧ 7 < p), gR p) ≤ (G : ℝ) / Q) :
    (Blo : ℝ) / Q ≤ Dusart.Bconst := by
  simp only [bOK, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hE, hb⟩ := hb
  have hγ := gamma_lower Q hQ
  have hBl := B_lower Q hQ hE hG
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hE' : (12 : ℝ) ≤ E := by exact_mod_cast hE
  have hcast : ((4096 * (E - 1) * (Blo + 10 * logRedHi Q 2 1 + (wG Q 2 + wG Q 3 + wG Q 5 + wG Q 7) + G) +
      2 * (E - 1) * Q + 2048 * Q : ℕ) : ℝ) ≤ ((4096 * (E - 1) * hsum Q 1024 : ℕ) : ℝ) := by exact_mod_cast hb
  have hE1 : ((E - 1 : ℕ) : ℝ) = (E : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  push_cast [hE1] at hcast
  unfold Dusart.Bconst
  have hpos : (0 : ℝ) < 4096 * ((E : ℝ) - 1) * Q := by nlinarith
  -- divide hcast by 4096 (E-1) Q
  have key : (Blo : ℝ) / Q ≤ (hsum Q 1024 : ℝ) / Q - 10 * ((logRedHi Q 2 1 : ℕ) : ℝ) / Q - 1 / 2048 -
      ((wG Q 2 + wG Q 3 + wG Q 5 + wG Q 7 : ℕ) : ℝ) / Q - (G : ℝ) / Q - 1 / (2 * ((E : ℝ) - 1)) := by
    have hE0 : (0 : ℝ) < (E : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hQ']
    have : (Blo : ℝ) * (4096 * ((E : ℝ) - 1)) ≤ ((hsum Q 1024 : ℝ) - 10 * (logRedHi Q 2 1 : ℝ) -
        ((wG Q 2 : ℝ) + wG Q 3 + wG Q 5 + wG Q 7) - G) * (4096 * ((E : ℝ) - 1)) - 2 * ((E : ℝ) - 1) * Q - 2048 * Q := by
      nlinarith
    push_cast
    field_simp
    nlinarith
  linarith

lemma run_append (Q Blo : ℕ) : ∀ (l1 l2 : List (List ℕ × Option (ℕ × ℕ × ℕ))) (s : ℕ × ℕ × ℕ × ℕ × ℕ),
    run Q Blo (l1 ++ l2) s = (run Q Blo l1 s).bind (run Q Blo l2) := by
  intro l1
  induction l1 with
  | nil => intro l2 s; simp [run]
  | cons item rest ih =>
    intro l2 s
    obtain ⟨codes, chk⟩ := item
    obtain ⟨n, i, A, G, lb⟩ := s
    simp only [List.cons_append, run]
    rcases step Q codes i n 0 0 with _ | ⟨a', g', n'⟩
    · rfl
    · rcases chk with _ | ⟨k1a, k1b, k2⟩
      · exact ih l2 _
      · simp only
        split_ifs
        · exact ih l2 _
        · rfl

/-- The invariant alone (no B hypothesis). -/
theorem run_inv (Q Blo : ℕ) (hQ : 0 < Q) :
    ∀ (items : List (List ℕ × Option (ℕ × ℕ × ℕ))) (n i A G lb n2 i2 A2 G2 lb2 : ℕ),
      run Q Blo items (n, i, A, G, lb) = some (n2, i2, A2, G2, lb2) → Inv Q n i A G → Inv Q n2 i2 A2 G2 := by
  intro items
  induction items with
  | nil =>
    intro n i A G lb n2 i2 A2 G2 lb2 h hI
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact hI
  | cons item rest ih =>
    intro n i A G lb n2 i2 A2 G2 lb2 h hI
    obtain ⟨codes, chk⟩ := item
    obtain ⟨hi, hn, h11, hA, hG⟩ := hI
    rw [run] at h
    rcases hst : step Q codes i n 0 0 with _ | ⟨a', g', n'⟩
    · rw [hst] at h; exact absurd h (by simp)
    rw [hst] at h
    obtain ⟨hnn', -, -, hA', hG'⟩ := step_sound Q hQ codes i n 0 0 a' g' n' hi hn (by omega) hst
    have hidx := step_end_index Q codes i n 0 0 a' g' n' hi hn hst
    have hI' : Inv Q n' ((i + codes.length) % 48) (A + a') (G + g') := by
      refine ⟨Nat.mod_lt _ (by norm_num), hidx, by omega, ?_, ?_⟩
      · rw [sum_Ico_split _ h11 hnn']; push_cast; rw [add_div]; rw [Nat.sub_zero] at hA'; linarith
      · rw [sum_Ico_split _ h11 hnn']; push_cast; rw [add_div]; rw [Nat.sub_zero] at hG'; linarith
    rcases chk with _ | ⟨k1a, k1b, k2⟩
    · exact ih _ _ _ _ _ _ _ _ _ _ h hI'
    · simp only at h
      split_ifs at h
      exact ih _ _ _ _ _ _ _ _ _ _ h hI'

/-- **Finite-range theorem from a successful run.** -/
theorem finite_range_of_run {Q Blo : ℕ} (hQ : 0 < Q) {items : List (List ℕ × Option (ℕ × ℕ × ℕ))}
    {n2 i2 A2 G2 lb2 : ℕ} (hrun : run Q Blo items (11, 1, 0, 0, 10372) = some (n2, i2, A2, G2, lb2))
    (hb : bOK Q Blo n2 G2 = true) :
    ∀ x : ℝ, 10372 ≤ x → x < lb2 →
      Dusart.primeRecip x - Real.log (Real.log x) - Dusart.Bconst ≤ Dusart.dusartRhs x := by
  have hI := run_inv Q Blo hQ items _ _ _ _ _ _ _ _ _ _ hrun (Inv_start Q)
  have hB := B_from_bOK hQ hb hI.2.2.2.2
  intro x hx1 hx2
  exact (run_sound Q Blo hQ hB items _ _ _ _ _ _ _ _ _ _ hrun (Inv_start Q)).2.2 x (by exact_mod_cast hx1) hx2

end DusartCert
end

set_option maxRecDepth 200000 in
theorem runAll_dusart : DusartCert.run (2 ^ 64) 4823768287920834435 (DusartCert.Gen.items0 ++ (DusartCert.Gen.items1 ++ (DusartCert.Gen.items2 ++ (DusartCert.Gen.items3 ++ (DusartCert.Gen.items4 ++ (DusartCert.Gen.items5 ++ (DusartCert.Gen.items6 ++ (DusartCert.Gen.items7 ++ (DusartCert.Gen.items8 ++ (DusartCert.Gen.items9 ++ (DusartCert.Gen.items10 ++ (DusartCert.Gen.items11 ++ (DusartCert.Gen.items12 ++ (DusartCert.Gen.items13 ++ (DusartCert.Gen.items14 ++ (DusartCert.Gen.items15 ++ (DusartCert.Gen.items16 ++ (DusartCert.Gen.items17 ++ (DusartCert.Gen.items18 ++ (DusartCert.Gen.items19 ++ (DusartCert.Gen.items20 ++ (DusartCert.Gen.items21 ++ (DusartCert.Gen.items22 ++ (DusartCert.Gen.items23)))))))))))))))))))))))) (11, 1, 0, 0, 10372) =
    some (3594643, 17, 33198239062610841350, 295192172967369872, 3594643) := by
  rw [DusartCert.run_append, DusartCert.run_0, Option.bind_some, DusartCert.run_append, DusartCert.run_1, Option.bind_some, DusartCert.run_append, DusartCert.run_2, Option.bind_some, DusartCert.run_append, DusartCert.run_3, Option.bind_some, DusartCert.run_append, DusartCert.run_4, Option.bind_some, DusartCert.run_append, DusartCert.run_5, Option.bind_some, DusartCert.run_append, DusartCert.run_6, Option.bind_some, DusartCert.run_append, DusartCert.run_7, Option.bind_some, DusartCert.run_append, DusartCert.run_8, Option.bind_some, DusartCert.run_append, DusartCert.run_9, Option.bind_some, DusartCert.run_append, DusartCert.run_10, Option.bind_some, DusartCert.run_append, DusartCert.run_11, Option.bind_some, DusartCert.run_append, DusartCert.run_12, Option.bind_some, DusartCert.run_append, DusartCert.run_13, Option.bind_some, DusartCert.run_append, DusartCert.run_14, Option.bind_some, DusartCert.run_append, DusartCert.run_15, Option.bind_some, DusartCert.run_append, DusartCert.run_16, Option.bind_some, DusartCert.run_append, DusartCert.run_17, Option.bind_some, DusartCert.run_append, DusartCert.run_18, Option.bind_some, DusartCert.run_append, DusartCert.run_19, Option.bind_some, DusartCert.run_append, DusartCert.run_20, Option.bind_some, DusartCert.run_append, DusartCert.run_21, Option.bind_some, DusartCert.run_append, DusartCert.run_22, Option.bind_some, DusartCert.run_23]

theorem bAll_dusart : DusartCert.bOK (2 ^ 64) 4823768287920834435 3594643 295192172967369872 = true := by decide +kernel

theorem solution (x : ℝ) (h1 : 10372 ≤ x) (h2 : x ≤ 3594641) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (10 * Real.log x ^ 2) + 4 / (15 * Real.log x ^ 3) :=
  DusartCert.finite_range_of_run (by norm_num) runAll_dusart bAll_dusart x h1 (by push_cast; linarith)
