-- Prove2me | solution 1 for Dusart.reciprocal_primes_of_chebyshev
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:50.22383+00:00
-- url     : https://prove2.me/submissions/d5e36b37-dcf1-4340-8d56-28a577a4462e

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Theorems.Thm_Dusart_finite_range_10372

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

open Real MeasureTheory Set Filter Topology

set_option autoImplicit false

namespace Dusart

/-- `∫_0^∞ log v · e^{-v} dv = -γ` (from `Γ'(1) = -γ`). -/
theorem integral_log_mul_exp_neg : ∫ v in Set.Ioi (0 : ℝ), Real.log v * Real.exp (-v) = -eulerMascheroniConstant := by
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  have hGI := Complex.hasDerivAt_GammaIntegral h1
  have hev : Complex.Gamma =ᶠ[𝓝 1] Complex.GammaIntegral := by
    have ho : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds h1] with s hs using Complex.Gamma_eq_integral hs
  have hG := hGI.congr_of_eventuallyEq hev
  have hu := hG.unique Complex.hasDerivAt_Gamma_one
  have hint : (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) =
      ((∫ t : ℝ in Set.Ioi 0, Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp
  rw [hint] at hu
  exact_mod_cast hu

end Dusart
end

section

open Real MeasureTheory Set Filter Topology

set_option autoImplicit false

namespace Dusart

/-- `fL(v) = log v · e^{-v}`. -/
noncomputable def fL (v : ℝ) : ℝ := Real.log v * Real.exp (-v)

lemma abs_log_le {v : ℝ} (hv : 0 < v) : |Real.log v| ≤ 2 * v ^ ((1 / 2 : ℝ) - 1) + v ^ ((2 : ℝ) - 1) := by
  have h1 : v ^ ((2 : ℝ) - 1) = v := by norm_num
  have h2 : v ^ ((1 / 2 : ℝ) - 1) = (1 / v) ^ (1 / 2 : ℝ) := by
    rw [show (1 / v) = v⁻¹ from one_div v, Real.inv_rpow hv.le, ← Real.rpow_neg hv.le]; norm_num
  rw [h1, h2]
  have hp : 0 ≤ (1 / v) ^ (1 / 2 : ℝ) := by positivity
  rcases le_or_gt 1 v with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    linarith [Real.log_le_sub_one_of_pos hv]
  · rw [abs_of_neg (Real.log_neg hv h)]
    have := Real.log_le_rpow_div (x := 1 / v) (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [one_div, Real.log_inv] at this
    rw [one_div] at hp ⊢
    linarith

lemma integrableOn_fL : IntegrableOn fL (Set.Ioi 0) := by
  have hb : IntegrableOn (fun v : ℝ => 2 * (Real.exp (-v) * v ^ ((1 / 2 : ℝ) - 1)) +
      Real.exp (-v) * v ^ ((2 : ℝ) - 1)) (Set.Ioi 0) :=
    ((Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2).add
      (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2))
  refine Integrable.mono' hb ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun v hv => ?_) measurableSet_Ioi
    exact ((Real.continuousAt_log (ne_of_gt hv)).mul (Real.continuous_exp.comp continuous_neg).continuousAt).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv => ?_)
    have hv' : (0 : ℝ) < v := hv
    rw [Real.norm_eq_abs, fL, abs_mul, abs_of_pos (Real.exp_pos _)]
    have := abs_log_le hv'
    have he := Real.exp_pos (-v)
    nlinarith

/-- `∫_c^∞ log v e^{-v} dv → -γ` as `c → 0⁺`. -/
lemma tendsto_integral_fL :
    Tendsto (fun c => ∫ v in Set.Ioi c, fL v) (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
  rw [← integral_log_mul_exp_neg]
  have hF : ∀ᶠ c in 𝓝[>] (0 : ℝ), ∫ v in Set.Ioi c, fL v = ∫ v in Set.Ioi 0, (Set.Ioi c).indicator fL v := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.2 (Set.Ioi_subset_Ioi (le_of_lt hc))]
  refine Tendsto.congr' (EventuallyEq.symm hF) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun v => ‖fL v‖) ?_ ?_ integrableOn_fL.norm ?_
  · exact Filter.Eventually.of_forall fun c =>
      (integrableOn_fL.indicator measurableSet_Ioi).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun c => Filter.Eventually.of_forall fun v =>
      norm_indicator_le_norm_self _ _
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv => ?_)
    have hv' : (0 : ℝ) < v := hv
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_lt_nhds hv').filter_mono nhdsWithin_le_nhds] with c hc
    rw [Set.indicator_of_mem (show v ∈ Set.Ioi c from hc)]; rfl

/-- **Laplace form.** For `ε > 0`, `ε ∫_2^∞ log log t · t^{-1-ε} dt = ∫_{ε log 2}^∞ log v e^{-v} dv - log ε · e^{-ε log 2}`. -/
theorem J_eq {ε : ℝ} (hε : 0 < ε) :
    ε * ∫ t in Set.Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-1 - ε) =
      (∫ v in Set.Ioi (ε * Real.log 2), fL v) - Real.log ε * Real.exp (-(ε * Real.log 2)) := by
  have hA : ∫ t in Set.Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-1 - ε) =
      ∫ x in Set.Ioi (Real.log 2), Real.log x * Real.exp (-(ε * x)) := by
    have := integral_comp_exp_Ioi (fun t => Real.log (Real.log t) * t ^ (-1 - ε)) (Real.log 2)
    rw [Real.exp_log (by norm_num)] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [smul_eq_mul, Real.log_exp]
    rw [← Real.exp_mul]
    have : Real.exp x * (Real.log x * Real.exp (x * (-1 - ε))) = Real.log x * (Real.exp x * Real.exp (x * (-1 - ε))) := by ring
    rw [this, ← Real.exp_add]; congr 2; ring
  have hB : ε * ∫ x in Set.Ioi (Real.log 2), Real.log x * Real.exp (-(ε * x)) =
      ∫ v in Set.Ioi (ε * Real.log 2), Real.log (v / ε) * Real.exp (-v) := by
    have := integral_comp_mul_left_Ioi (fun v => Real.log (v / ε) * Real.exp (-v)) (Real.log 2) hε
    simp only [smul_eq_mul] at this
    rw [← mul_right_inj' (inv_ne_zero hε.ne'), ← this, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [mul_div_cancel_left₀ _ hε.ne']
  have hc : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos (by norm_num))
  have hC : ∫ v in Set.Ioi (ε * Real.log 2), Real.log (v / ε) * Real.exp (-v) =
      ∫ v in Set.Ioi (ε * Real.log 2), (fL v - Real.log ε * Real.exp (-v)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv' : 0 < v := lt_trans hc hv
    simp only [fL]; rw [Real.log_div hv'.ne' hε.ne']; ring
  rw [hA, hB, hC, integral_sub (integrableOn_fL.mono_set (Set.Ioi_subset_Ioi hc.le))
    ((integrableOn_exp_neg_Ioi _).const_mul _), integral_const_mul, integral_exp_neg_Ioi]

/-- **The `log log` Laplace asymptotic.** `ε ∫_2^∞ log log t · t^{-1-ε} dt - log(1/ε) → -γ` as `ε → 0⁺`. -/
theorem tendsto_J :
    Tendsto (fun ε => ε * (∫ t in Set.Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-1 - ε)) - Real.log (1 / ε))
      (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcmap : Tendsto (fun ε : ℝ => ε * Real.log 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (continuous_id.mul continuous_const).tendsto' (0 : ℝ) 0 (by simp) (f := fun ε : ℝ => ε * Real.log 2)
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε using mul_pos hε hl2
  have h1 := tendsto_integral_fL.comp hcmap
  have h2 : Tendsto (fun ε : ℝ => Real.log ε * (1 - Real.exp (-(ε * Real.log 2)))) (𝓝[>] 0) (𝓝 0) := by
    have hlog := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos).mul_const (Real.log 2)
    rw [zero_mul] at hlog
    refine squeeze_zero_norm' ?_ (hlog.norm.trans (by simp))
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    have hc : 0 ≤ ε * Real.log 2 := (mul_pos hε' hl2).le
    have e1 : 0 ≤ 1 - Real.exp (-(ε * Real.log 2)) := by
      have := Real.exp_le_one_iff.2 (neg_nonpos.2 hc); linarith
    have e2 : 1 - Real.exp (-(ε * Real.log 2)) ≤ ε * Real.log 2 := by
      have := Real.add_one_le_exp (-(ε * Real.log 2)); linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg e1, Real.rpow_one]
    calc |Real.log ε| * (1 - Real.exp (-(ε * Real.log 2))) ≤ |Real.log ε| * (ε * Real.log 2) :=
          mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
      _ = |Real.log ε * ε * Real.log 2| := by
          rw [abs_mul, abs_mul, abs_of_pos hε', abs_of_pos hl2]; ring
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  simp only [Function.comp]
  rw [J_eq hε', one_div, Real.log_inv]; ring

end Dusart
end

section

open Real MeasureTheory Set Filter Topology Asymptotics

set_option autoImplicit false

namespace Dusart

lemma primeRecip_nonneg (x : ℝ) : 0 ≤ primeRecip x :=
  Finset.sum_nonneg fun p _ => by positivity

lemma primeRecip_mono : Monotone primeRecip := by
  intro x y hxy
  unfold primeRecip
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
  refine Finset.filter_subset_filter _ (Finset.range_subset_range.2 ?_)
  exact Nat.add_le_add_right (Nat.floor_le_floor hxy) 1

lemma measurable_primeRecip : Measurable primeRecip := primeRecip_mono.measurable

lemma primeRecip_eq_zero {t : ℝ} (ht : t < 2) : primeRecip t = 0 := by
  unfold primeRecip
  refine Finset.sum_eq_zero fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  have hf : ⌊t⌋₊ < 2 := by
    rcases lt_or_ge t 0 with h | h
    · rw [Nat.floor_eq_zero.2 (by linarith)]; norm_num
    · exact (Nat.floor_lt h).2 (by exact_mod_cast ht)
  have := hp.2.two_le; omega

/-- `∑_{k ∈ [1, ⌊t⌋]} [k prime]/k = ∑_{p ≤ t} 1/p`. -/
lemma sum_Icc_eq_primeRecip (t : ℝ) :
    ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (if k.Prime then (1 : ℝ) / k else 0) = primeRecip t := by
  unfold primeRecip
  rw [Finset.sum_filter]
  have hsub : Finset.Icc 1 ⌊t⌋₊ ⊆ Finset.range (⌊t⌋₊ + 1) := fun k hk => by
    simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
  refine Finset.sum_subset hsub fun k hk hk' => ?_
  simp only [Finset.mem_Icc, Finset.mem_range, not_and, not_le] at hk hk'
  have : k = 0 := by by_contra h; have := hk' (by omega); omega
  subst this; simp

/-- **Abel summation for the prime zeta function.** `∑_p p^{-1-ε} = ε ∫_1^∞ S(t) t^{-1-ε} dt`. -/
theorem primeZeta_eq_integral {ε : ℝ} (hε : 0 < ε) :
    ∑' p : Nat.Primes, (p : ℝ) ^ (-1 - ε) = ε * ∫ t in Set.Ioi (1 : ℝ), primeRecip t * t ^ (-1 - ε) := by
  set f : ℕ → ℝ := fun n => if n.Prime then (1 : ℝ) / n else 0
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [f]; split_ifs <;> positivity
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (ε / 2) := by
    have hlog : (fun n : ℕ => Real.log n) =O[atTop] fun n : ℕ => (n : ℝ) ^ (ε / 2) :=
      ((isLittleO_log_rpow_atTop (by linarith : 0 < ε / 2)).isBigO).comp_tendsto tendsto_natCast_atTop_atTop
    have hone : (fun _ : ℕ => (1 : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (ε / 2) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [norm_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      exact Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
    refine IsBigO.trans ?_ (hone.add hlog)
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => hf0 k)]
    have h1 : ∑ k ∈ Finset.Icc 1 n, f k ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k :=
      Finset.sum_le_sum fun k _ => by simp only [f]; split_ifs; exacts [le_rfl, by positivity]
    have h2 : ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k = harmonic n := by
      rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    have h3 := harmonic_le_one_add_log n
    have h4 : 0 ≤ 1 + Real.log n := by
      have := Real.log_natCast_nonneg n; linarith
    rw [abs_of_nonneg h4]; linarith
  have hs : ε / 2 < (ε : ℂ).re := by simp; linarith
  have h := LSeries_eq_mul_integral_of_nonneg f (by linarith) hs hO hf0
  -- left side
  have hL : LSeries (fun n => (f n : ℂ)) ε = ((∑' p : Nat.Primes, (p : ℝ) ^ (-1 - ε) : ℝ) : ℂ) := by
    have hsub : ∑' p : Nat.Primes, (p : ℝ) ^ (-1 - ε) =
        ∑' n : ℕ, (if n.Prime then (n : ℝ) ^ (-1 - ε) else 0) := by
      refine (tsum_subtype {n : ℕ | n.Prime} (fun n : ℕ => (n : ℝ) ^ (-1 - ε))).trans ?_
      congr 1; funext n; simp [Set.indicator]
    rw [LSeries, hsub, Complex.ofReal_tsum]
    congr 1; funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f, Nat.not_prime_zero]
    rw [LSeries.term_of_ne_zero hn]
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [f]
    split_ifs with hp
    · rw [show ((n : ℂ) ^ (ε : ℂ)) = (((n : ℝ) ^ ε : ℝ) : ℂ) by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp, Complex.ofReal_cpow hn'.le]]
      rw [← Complex.ofReal_div]; congr 1
      rw [Real.rpow_sub hn', Real.rpow_neg_one]; field_simp
    · simp
  -- right side
  have hR : (ε : ℂ) * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (f k : ℂ)) * (t : ℂ) ^ (-((ε : ℂ) + 1)) =
      ((ε * ∫ t in Set.Ioi (1 : ℝ), primeRecip t * t ^ (-1 - ε) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← integral_complex_ofReal]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := le_of_lt (lt_trans one_pos ht)
    have hc : (t : ℂ) ^ (-((ε : ℂ) + 1)) = ((t ^ (-1 - ε) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht0]; push_cast; ring_nf
    rw [hc, ← sum_Icc_eq_primeRecip t, Complex.ofReal_mul, Complex.ofReal_sum]
  rw [hL, hR] at h
  exact_mod_cast h

/-- **Substitution `t = e^{u/ε}`.** `ε ∫_2^∞ F(t) t^{-1-ε} dt = ∫_{ε log 2}^∞ F(e^{u/ε}) e^{-u} du`. -/
theorem subst_integral {ε : ℝ} (hε : 0 < ε) (F : ℝ → ℝ) :
    ε * ∫ t in Set.Ioi (2 : ℝ), F t * t ^ (-1 - ε) =
      ∫ u in Set.Ioi (ε * Real.log 2), F (Real.exp (u / ε)) * Real.exp (-u) := by
  have hA : ∫ t in Set.Ioi (2 : ℝ), F t * t ^ (-1 - ε) =
      ∫ x in Set.Ioi (Real.log 2), F (Real.exp x) * Real.exp (-(ε * x)) := by
    have := integral_comp_exp_Ioi (fun t => F t * t ^ (-1 - ε)) (Real.log 2)
    rw [Real.exp_log (by norm_num)] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [smul_eq_mul]
    rw [← Real.exp_mul]
    have : Real.exp x * (F (Real.exp x) * Real.exp (x * (-1 - ε))) =
        F (Real.exp x) * (Real.exp x * Real.exp (x * (-1 - ε))) := by ring
    rw [this, ← Real.exp_add]; congr 2; ring
  have hB := integral_comp_mul_left_Ioi (fun u => F (Real.exp (u / ε)) * Real.exp (-u)) (Real.log 2) hε
  simp only [smul_eq_mul] at hB
  rw [hA, ← mul_right_inj' (inv_ne_zero hε.ne'), ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul, ← hB]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [mul_div_cancel_left₀ _ hε.ne']

end Dusart
end

section

open Real MeasureTheory Set Filter Topology

set_option autoImplicit false

namespace Dusart

/-- If `∑_{p ≤ x} 1/p - log log x → M`, then `∑_p p^{-1-ε} - log(1/ε) → M - γ` as `ε → 0⁺`. -/
theorem tendsto_primeZeta {M : ℝ}
    (hM : Tendsto (fun x => primeRecip x - Real.log (Real.log x)) atTop (𝓝 M)) :
    Tendsto (fun ε => (∑' p : Nat.Primes, (p : ℝ) ^ (-1 - ε)) - Real.log (1 / ε)) (𝓝[>] 0)
      (𝓝 (M - eulerMascheroniConstant)) := by
  set r : ℝ → ℝ := fun t => primeRecip t - Real.log (Real.log t) - M with hrdef
  have hr0 : Tendsto r atTop (𝓝 0) := by simpa [hrdef] using hM.sub_const M
  have hrmeas : Measurable r := by
    simp only [hrdef]
    exact (measurable_primeRecip.sub (Real.measurable_log.comp Real.measurable_log)).sub_const M
  -- r is bounded on [2, ∞)
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, 2 ≤ t → |r t| ≤ R := by
    obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 (hr0.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos))
    set Y := max X 2
    refine ⟨max 1 (primeRecip Y + |Real.log (Real.log 2)| + |Real.log (Real.log Y)| + |M|), le_max_of_le_left zero_le_one,
      fun t ht => ?_⟩
    rcases le_or_gt Y t with h | h
    · have := hX t (le_trans (le_max_left _ _) h)
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact le_max_of_le_left this
    · refine le_max_of_le_right ?_
      have hS0 := primeRecip_nonneg t
      have hS := primeRecip_mono h.le
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
      have hltY : Real.log t ≤ Real.log Y := Real.log_le_log (by linarith) h.le
      have hll1 : Real.log (Real.log 2) ≤ Real.log (Real.log t) := Real.log_le_log hl2 hlt
      have hll2 : Real.log (Real.log t) ≤ Real.log (Real.log Y) := Real.log_le_log (by linarith) hltY
      simp only [hrdef]
      rw [abs_le]; constructor
      · linarith [le_abs_self (Real.log (Real.log Y)), neg_abs_le (Real.log (Real.log 2)), le_abs_self M, neg_abs_le M,
          abs_nonneg (Real.log (Real.log 2))]
      · linarith [le_abs_self (Real.log (Real.log Y)), neg_abs_le (Real.log (Real.log 2)), le_abs_self M, neg_abs_le M,
          abs_nonneg (Real.log (Real.log Y))]
  -- the remainder term
  set Rt : ℝ → ℝ := fun ε => ∫ u in Set.Ioi (ε * Real.log 2), r (Real.exp (u / ε)) * Real.exp (-u)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbig : ∀ ε : ℝ, 0 < ε → ∀ u ∈ Set.Ioi (ε * Real.log 2), 2 ≤ Real.exp (u / ε) := fun ε hε u hu => by
    have : Real.log 2 < u / ε := by rw [lt_div_iff₀ hε]; linarith [show ε * Real.log 2 < u from hu]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (u / ε) := Real.exp_le_exp.2 this.le
  have hint_r : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun u => r (Real.exp (u / ε)) * Real.exp (-u)) (Set.Ioi (ε * Real.log 2)) := by
    intro ε hε
    refine Integrable.mono' ((integrableOn_exp_neg_Ioi _).const_mul R) ?_ ?_
    · exact ((hrmeas.comp (Real.measurable_exp.comp (measurable_id.div_const ε))).mul
        (Real.measurable_exp.comp measurable_neg)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hR _ (hbig ε hε u hu)) (Real.exp_pos _).le
  have hRt : Tendsto Rt (𝓝[>] 0) (𝓝 0) := by
    have hF : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Rt ε =
        ∫ u in Set.Ioi 0, (Set.Ioi (ε * Real.log 2)).indicator (fun u => r (Real.exp (u / ε)) * Real.exp (-u)) u := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      simp only [Rt]
      rw [setIntegral_indicator measurableSet_Ioi,
        Set.inter_eq_right.2 (Set.Ioi_subset_Ioi (mul_pos hε' hl2).le)]
    refine Tendsto.congr' (EventuallyEq.symm hF) ?_
    have key : Tendsto (fun ε => ∫ u in Set.Ioi 0,
        (Set.Ioi (ε * Real.log 2)).indicator (fun u => r (Real.exp (u / ε)) * Real.exp (-u)) u) (𝓝[>] 0)
        (𝓝 (∫ u in Set.Ioi (0 : ℝ), (0 : ℝ))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun u => R * Real.exp (-u)) ?_ ?_
        ((integrableOn_exp_neg_Ioi 0).const_mul R) ?_
      · exact Filter.Eventually.of_forall fun ε =>
          (((hrmeas.comp (Real.measurable_exp.comp (measurable_id.div_const ε))).mul
            (Real.measurable_exp.comp measurable_neg)).indicator measurableSet_Ioi).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        refine Filter.Eventually.of_forall fun u => ?_
        by_cases hu : u ∈ Set.Ioi (ε * Real.log 2)
        · rw [Set.indicator_of_mem hu, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_right (hR _ (hbig ε hε u hu)) (Real.exp_pos _).le
        · rw [Set.indicator_of_notMem hu, norm_zero]; positivity
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
        have hu' : (0 : ℝ) < u := hu
        have hinf : Tendsto (fun ε : ℝ => Real.exp (u / ε)) (𝓝[>] 0) atTop := by
          have := (tendsto_inv_nhdsGT_zero.const_mul_atTop hu')
          exact Real.tendsto_exp_atTop.comp (this.congr fun ε => by rw [div_eq_mul_inv])
        have hlim := ((hr0.comp hinf).mul_const (Real.exp (-u)))
        rw [zero_mul] at hlim
        refine hlim.congr' ?_
        have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * Real.log 2 < u := by
          have hc : Tendsto (fun ε : ℝ => ε * Real.log 2) (𝓝[>] 0) (𝓝 0) := by
            have := (continuous_id.mul continuous_const).tendsto' (0 : ℝ) 0 (by simp) (f := fun ε : ℝ => ε * Real.log 2)
            exact this.mono_left nhdsWithin_le_nhds
          exact hc.eventually (eventually_lt_nhds hu')
        filter_upwards [hev] with ε hε
        rw [Set.indicator_of_mem (show u ∈ Set.Ioi (ε * Real.log 2) from hε)]; rfl
    rw [integral_zero] at key
    exact key
  -- the decomposition
  have hdec : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∑' p : Nat.Primes, (p : ℝ) ^ (-1 - ε)) - Real.log (1 / ε) =
      (ε * (∫ t in Set.Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-1 - ε)) - Real.log (1 / ε)) +
        M * Real.exp (-(ε * Real.log 2)) + Rt ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    have hc : 0 < ε * Real.log 2 := mul_pos hε' hl2
    -- Ioi 1 → Ioi 2
    have h12 : ∫ t in Set.Ioi (1 : ℝ), primeRecip t * t ^ (-1 - ε) =
        ∫ t in Set.Ioi (2 : ℝ), primeRecip t * t ^ (-1 - ε) := by
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
      refine integral_congr_ae ?_
      filter_upwards [volume.ae_ne (2 : ℝ)] with t ht
      by_cases h2 : 2 < t
      · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (1 : ℝ) from by simp; linarith),
          Set.indicator_of_mem (show t ∈ Set.Ioi (2 : ℝ) from h2)]
      · have h2' : t < 2 := lt_of_le_of_ne (not_lt.1 h2) ht
        rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (2 : ℝ) from by simp; linarith)]
        by_cases h1 : 1 < t
        · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (1 : ℝ) from h1), primeRecip_eq_zero h2', zero_mul]
        · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (1 : ℝ) from by simpa using h1)]
    rw [primeZeta_eq_integral hε', h12, subst_integral hε', subst_integral hε']
    have hsplit : ∫ u in Set.Ioi (ε * Real.log 2), primeRecip (Real.exp (u / ε)) * Real.exp (-u) =
        (∫ u in Set.Ioi (ε * Real.log 2), Real.log (Real.log (Real.exp (u / ε))) * Real.exp (-u)) +
        (∫ u in Set.Ioi (ε * Real.log 2), M * Real.exp (-u)) + Rt ε := by
      have hA : IntegrableOn (fun u => Real.log (Real.log (Real.exp (u / ε))) * Real.exp (-u))
          (Set.Ioi (ε * Real.log 2)) := by
        refine ((integrableOn_fL.mono_set (Set.Ioi_subset_Ioi hc.le)).sub
          ((integrableOn_exp_neg_Ioi _).const_mul (Real.log ε))).congr_fun (fun u hu => ?_) measurableSet_Ioi
        have hu' : 0 < u := lt_trans hc hu
        simp only [fL, Real.log_exp, Pi.sub_apply]; rw [Real.log_div hu'.ne' hε'.ne']; ring
      have hB : IntegrableOn (fun u => M * Real.exp (-u)) (Set.Ioi (ε * Real.log 2)) :=
        (integrableOn_exp_neg_Ioi _).const_mul M
      calc ∫ u in Set.Ioi (ε * Real.log 2), primeRecip (Real.exp (u / ε)) * Real.exp (-u)
          = ∫ u in Set.Ioi (ε * Real.log 2), ((Real.log (Real.log (Real.exp (u / ε))) * Real.exp (-u) +
              M * Real.exp (-u)) + r (Real.exp (u / ε)) * Real.exp (-u)) :=
            setIntegral_congr_fun measurableSet_Ioi fun u _ => by simp only [hrdef]; ring
        _ = (∫ u in Set.Ioi (ε * Real.log 2), (Real.log (Real.log (Real.exp (u / ε))) * Real.exp (-u) +
              M * Real.exp (-u))) + Rt ε := integral_add (hA.add hB) (hint_r ε hε')
        _ = _ := by rw [integral_add hA hB]
    rw [hsplit, integral_const_mul, integral_exp_neg_Ioi]; ring
  have hlimM : Tendsto (fun ε : ℝ => M * Real.exp (-(ε * Real.log 2))) (𝓝[>] 0) (𝓝 M) := by
    have : Tendsto (fun ε : ℝ => M * Real.exp (-(ε * Real.log 2))) (𝓝 0) (𝓝 (M * Real.exp (-(0 * Real.log 2)))) :=
      ((Real.continuous_exp.comp ((continuous_id.mul continuous_const).neg)).const_mul M).tendsto 0
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have htot := (tendsto_J.add hlimM).add hRt
  rw [show -eulerMascheroniConstant + M + 0 = M - eulerMascheroniConstant by ring] at htot
  exact htot.congr' (EventuallyEq.symm hdec)

end Dusart
end

section

open Real Set Filter Topology

set_option autoImplicit false

namespace Dusart

/-- `h(y) = -log(1 - y) - y`. -/
noncomputable def hfun (y : ℝ) : ℝ := -Real.log (1 - y) - y

lemma hfun_nonneg {y : ℝ} (hy : y < 1) : 0 ≤ hfun y := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - y by linarith)
  simp only [hfun]; linarith

lemma hfun_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) : hfun y ≤ 2 * y ^ 2 := by
  have h1 : 0 < 1 - y := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [Real.log_inv] at h
  simp only [hfun]
  have h2 : (1 - y)⁻¹ - 1 - y = y ^ 2 / (1 - y) := by field_simp; ring
  have h3 : y ^ 2 / (1 - y) ≤ 2 * y ^ 2 := by
    rw [div_le_iff₀ h1]; nlinarith [sq_nonneg y]
  linarith

lemma prime_rpow_le {p : Nat.Primes} {ε : ℝ} (hε : 0 ≤ ε) : (p : ℝ) ^ (-1 - ε) ≤ 1 / 2 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  calc (p : ℝ) ^ (-1 - ε) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := by gcongr

lemma prime_rpow_sq_le {p : Nat.Primes} {ε : ℝ} (hε : 0 ≤ ε) : ((p : ℝ) ^ (-1 - ε)) ^ 2 ≤ (p : ℝ) ^ (-2 : ℝ) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.prop.one_lt.le
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hp (by push_cast; linarith)

lemma summable_bound : Summable (fun p : Nat.Primes => 2 * (p : ℝ) ^ (-2 : ℝ)) :=
  (Nat.Primes.summable_rpow.2 (by norm_num)).mul_left 2

lemma hfun_bound {p : Nat.Primes} {ε : ℝ} (hε : 0 ≤ ε) : ‖hfun ((p : ℝ) ^ (-1 - ε))‖ ≤ 2 * (p : ℝ) ^ (-2 : ℝ) := by
  have h0 : 0 ≤ (p : ℝ) ^ (-1 - ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hle := prime_rpow_le (p := p) hε
  rw [Real.norm_eq_abs, abs_of_nonneg (hfun_nonneg (by linarith))]
  exact (hfun_le h0 hle).trans (by linarith [prime_rpow_sq_le (p := p) hε])

/-- Euler product: `ζ(σ) = exp(∑_p -log(1 - p^{-σ}))` for real `σ > 1`. -/
lemma zeta_eq_exp {σ : ℝ} (hσ : 1 < σ) :
    riemannZeta σ = ((Real.exp (∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-σ))) : ℝ) : ℂ) := by
  have h := riemannZeta_eulerProduct_exp_log (s := (σ : ℂ)) (by simpa using hσ)
  rw [← h, Complex.ofReal_exp, Complex.ofReal_tsum]
  congr 1
  refine tsum_congr fun p => ?_
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hy : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  rw [show ((p : ℂ) ^ (-(σ : ℂ))) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) by
      rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp, ← Complex.ofReal_neg, Complex.ofReal_cpow hp],
    ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_log (by linarith), Complex.ofReal_neg]

/-- **The ζ side.** `∑_p p^{-1-ε} - log(1/ε) → ∑_p (log(1 - 1/p) + 1/p)` as `ε → 0⁺`. -/
theorem tendsto_primeZeta_zeta :
    Tendsto (fun ε => (∑' p : Nat.Primes, (p : ℝ) ^ (-1 - ε)) - Real.log (1 / ε)) (𝓝[>] 0)
      (𝓝 (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))) := by
  set A : ℝ → ℝ := fun σ => ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-σ))
  set K : ℝ → ℝ := fun ε => ∑' p : Nat.Primes, hfun ((p : ℝ) ^ (-1 - ε))
  -- (1) log ε + A(1+ε) → 0
  have hres : Tendsto (fun ε : ℝ => Real.log ε + A (1 + ε)) (𝓝[>] 0) (𝓝 0) := by
    have hmap : Tendsto (fun ε : ℝ => ((1 + ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun ε : ℝ => ((1 + ε : ℝ) : ℂ)) (𝓝 0) (𝓝 (((1 + 0 : ℝ) : ℂ))) :=
          (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h; have := congrArg Complex.re h; simp at this; linarith [show (0 : ℝ) < ε from hε]
    have h1 := (Complex.continuous_re.tendsto 1).comp (riemannZeta_residue_one.comp hmap)
    simp only [Complex.one_re] at h1
    have h2 : Tendsto (fun ε : ℝ => ε * Real.exp (A (1 + ε))) (𝓝[>] 0) (𝓝 1) := by
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      simp only [Function.comp]
      rw [zeta_eq_exp (by linarith)]
      simp [A]
      exact Or.inl (by rw [← Complex.ofReal_exp, Complex.ofReal_re])
    have h3 := (Real.continuousAt_log one_ne_zero).tendsto.comp h2
    rw [Real.log_one] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    simp only [Function.comp]
    rw [Real.log_mul hε'.ne' (Real.exp_pos _).ne', Real.log_exp]
  -- (2) A(1+ε) = P(ε) + K(ε)
  have hsplit : ∀ ε : ℝ, 0 < ε → A (1 + ε) = (∑' p : Nat.Primes, (p : ℝ) ^ (-1 - ε)) + K ε := by
    intro ε hε
    have hP : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-1 - ε)) := Nat.Primes.summable_rpow.2 (by linarith)
    have hK : Summable (fun p : Nat.Primes => hfun ((p : ℝ) ^ (-1 - ε))) :=
      summable_bound.of_norm_bounded (fun p => hfun_bound (p := p) hε.le)
    simp only [A, K]
    rw [← hP.tsum_add hK]
    refine tsum_congr fun p => ?_
    simp only [hfun]; rw [show -(1 + ε) = -1 - ε by ring]; ring
  -- (3) K(ε) → ∑ h(1/p)
  have hK : Tendsto K (𝓝[>] 0) (𝓝 (∑' p : Nat.Primes, hfun ((p : ℝ) ^ (-1 - (0 : ℝ))))) := by
    refine tendsto_tsum_of_dominated_convergence summable_bound (fun p => ?_) ?_
    · have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
      have hy : (p : ℝ) ^ (-1 - (0 : ℝ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by norm_num)
      have hc : ContinuousAt (fun ε : ℝ => hfun ((p : ℝ) ^ (-1 - ε))) 0 := by
        have hpow : ContinuousAt (fun ε : ℝ => (p : ℝ) ^ (-1 - ε)) 0 :=
          (Real.continuousAt_const_rpow hp).comp (continuous_const.sub continuous_id).continuousAt
        unfold hfun
        exact ((Real.continuousAt_log (by show (1 : ℝ) - (p : ℝ) ^ (-1 - (0 : ℝ)) ≠ 0; exact sub_ne_zero.2 (ne_of_gt hy))).comp
          (continuousAt_const.sub hpow)).neg.sub hpow
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact fun p => hfun_bound (p := p) (le_of_lt hε)
  have hK0 : (∑' p : Nat.Primes, hfun ((p : ℝ) ^ (-1 - (0 : ℝ)))) =
      -∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
    rw [← tsum_neg]
    refine tsum_congr fun p => ?_
    simp only [hfun, sub_zero, Real.rpow_neg_one, one_div]; ring
  rw [hK0] at hK
  have htot := hres.sub hK
  rw [zero_sub, neg_neg] at htot
  refine htot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  rw [hsplit ε hε', one_div, Real.log_inv]; ring

end Dusart
end

section

open Real MeasureTheory Set Filter Topology

set_option autoImplicit false

namespace Dusart

/-- **Identification of the Mertens constant.** Under any bound `|θ(t) - t| ≤ C t / log² t` for `t ≥ T`, the limit
`M` of `∑_{p ≤ x} 1/p - log log x` equals `B = γ + ∑_p (log(1 - 1/p) + 1/p)`. -/
theorem Mconst_eq_Bconst {T C : ℝ} (hT : 2 ≤ T) (hC : 0 ≤ C)
    (hθ : ∀ t, T ≤ t → |E t| ≤ C * t / Real.log t ^ 2) : Mconst = Bconst := by
  have h1 := tendsto_primeZeta (tendsto_primeRecip hT hC hθ)
  have h2 := tendsto_primeZeta_zeta
  have := tendsto_nhds_unique h1 h2
  simp only [Bconst]; linarith

/-- **Dusart's Theorem 6.10, conditional only on the Chebyshev estimate and the finite range.** -/
theorem dusart_reciprocal_primes_of_theta
    (hθ : ∀ t : ℝ, 3594641 ≤ t → |Chebyshev.theta t - t| ≤ (1 / 5) * t / Real.log t ^ 2)
    (hfin : ∀ x : ℝ, 10372 ≤ x → x ≤ 3594641 →
      primeRecip x - Real.log (Real.log x) - Bconst ≤ dusartRhs x)
    (x : ℝ) (hx : 10372 ≤ x) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (10 * Real.log x ^ 2) + 4 / (15 * Real.log x ^ 3) :=
  dusart_reciprocal_primes_of_inputs hθ (Mconst_eq_Bconst (by norm_num) (by norm_num) hθ) hfin x hx

end Dusart
end

theorem solution
    (hθ : ∀ t : ℝ, 3594641 ≤ t → |Chebyshev.theta t - t| ≤ (1 / 5) * t / Real.log t ^ 2)
    (x : ℝ) (hx : 10372 ≤ x) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (10 * Real.log x ^ 2) + 4 / (15 * Real.log x ^ 3) :=
  Dusart.dusart_reciprocal_primes_of_theta hθ (fun y hy1 hy2 => Dusart.finite_range_10372 y hy1 hy2) x hx
