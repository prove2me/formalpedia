-- Prove2me | solution 1 for Complex.mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ac05135e-6d51-5524-8ce4-499372b813ef

import Theorems.Thm_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div
import Theorems.Thm_Complex_integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Real Complex MeasureTheory Set Filter Topology

namespace P2mKcContig

abbrev μ0 : Measure ℝ := volume.restrict (Ioi (0:ℝ))

theorem ae_pos_μ0 : ∀ᵐ x ∂μ0, 0 < x := ae_restrict_mem measurableSet_Ioi

theorem norm_ofReal_cpow {x : ℝ} (hx : 0 < x) (r : ℂ) : ‖(x : ℂ) ^ r‖ = x ^ r.re :=
  norm_cpow_eq_rpow_re_of_pos hx r

theorem cpow_add_ofReal {x : ℝ} (hx : 0 < x) (r s : ℂ) :
    (x : ℂ) ^ r * (x : ℂ) ^ s = (x : ℂ) ^ (r + s) :=
  (cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')).symm

theorem ofReal_mul_cpow {x : ℝ} (hx : 0 < x) (r : ℂ) : (x : ℂ) * (x : ℂ) ^ r = (x : ℂ) ^ (r + 1) := by
  rw [cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_one, mul_comm]

theorem beta (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b))) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b)) =
        Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) :=
  Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div a b ha hb

theorem integrableOn_betaR {a c : ℝ} (ha : 0 < a) (hc : a < c) :
    IntegrableOn (fun v : ℝ => v ^ (a - 1) * (1 + v) ^ (-c)) (Ioi 0) := by
  have h0 := (beta (a : ℂ) ((c - a : ℝ) : ℂ) (by simpa) (by simp; linarith)).1.norm
  refine IntegrableOn.congr_fun h0 (fun v hv => ?_) measurableSet_Ioi
  have hv' : (0:ℝ) < v := hv
  rw [norm_mul, norm_ofReal_cpow hv', norm_ofReal_cpow (by linarith)]
  simp

def kk (β b d : ℂ) (x y : ℝ) : ℂ :=
  ((y : ℂ) ^ (β - 1) * (((1 + y : ℝ)) : ℂ) ^ (-b)) * (((1 + x + y : ℝ)) : ℂ) ^ (-d)

def kR (β b d : ℝ) (x y : ℝ) : ℝ := y ^ (β - 1) * (1 + y) ^ (-b) * (1 + x + y) ^ (-d)

theorem norm_kk (β b d : ℂ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) : ‖kk β b d x y‖ = kR β.re b.re d.re x y := by
  simp only [kk, kR, norm_mul, norm_ofReal_cpow hy, sub_re, one_re]
  rw [norm_ofReal_cpow (by linarith), norm_ofReal_cpow (by linarith), neg_re, neg_re]

theorem kR_nonneg (β b d : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) : 0 ≤ kR β b d x y := by
  unfold kR
  have : 0 < 1 + x + y := by linarith
  positivity

theorem kR_le (β b d : ℝ) (hd : 0 ≤ d) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    kR β b d x y ≤ y ^ (β - 1) * (1 + y) ^ (-(b + d)) := by
  unfold kR
  have h1 : (1 + x + y) ^ (-d) ≤ (1 + y) ^ (-d) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have h2 : 0 ≤ y ^ (β - 1) * (1 + y) ^ (-b) := by positivity
  calc y ^ (β - 1) * (1 + y) ^ (-b) * (1 + x + y) ^ (-d)
      ≤ y ^ (β - 1) * (1 + y) ^ (-b) * (1 + y) ^ (-d) := mul_le_mul_of_nonneg_left h1 h2
    _ = y ^ (β - 1) * (1 + y) ^ (-(b + d)) := by
        rw [mul_assoc, ← Real.rpow_add (by linarith)]; ring_nf

theorem kk_ofReal (β b d : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    kk (β : ℂ) (b : ℂ) (d : ℂ) x y = ((kR β b d x y : ℝ) : ℂ) := by
  simp only [kk, kR]
  rw [show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, show (-(b : ℂ)) = ((-b : ℝ) : ℂ) by push_cast; ring,
    show (-(d : ℂ)) = ((-d : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hy.le, ← ofReal_cpow (by linarith),
    ← ofReal_cpow (by linarith)]
  push_cast; ring

theorem measurable_kk (β b d : ℂ) : Measurable (Function.uncurry (kk β b d)) := by
  unfold kk
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · exact (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  · exact (Complex.measurable_ofReal.comp (by fun_prop)).pow_const _
  · exact (Complex.measurable_ofReal.comp (by fun_prop)).pow_const _

theorem measurable_kk_x (β b d : ℂ) (x : ℝ) : Measurable (kk β b d x) :=
  (measurable_kk β b d).of_uncurry_left

theorem integrable_kk (β b d : ℂ) (hβ : 0 < β.re) (hd : 0 ≤ d.re) (hbd : β.re < b.re + d.re) {x : ℝ}
    (hx : 0 ≤ x) : Integrable (kk β b d x) μ0 := by
  refine Integrable.mono' (integrableOn_betaR hβ hbd) (measurable_kk_x β b d x).aestronglyMeasurable ?_
  filter_upwards [ae_pos_μ0] with y hy
  rw [norm_kk β b d hx hy]
  exact kR_le _ _ _ hd hx hy

theorem ibp (B b d : ℂ) (hB : 0 < B.re) (hb : 0 < b.re) (hd : 0 < d.re) (hlt : B.re < b.re + d.re) {x : ℝ}
    (hx : 0 < x) :
    B * (∫ y in Ioi (0:ℝ), kk B b d x y) - b * (∫ y in Ioi (0:ℝ), kk (B + 1) (b + 1) d x y)
      - d * (∫ y in Ioi (0:ℝ), kk (B + 1) b (d + 1) x y) = 0 := by
  have hB0 : B ≠ 0 := fun h => by rw [h] at hB; simp at hB

  set u : ℝ → ℂ := fun y => (y : ℂ) ^ B with hu_def
  set u' : ℝ → ℂ := fun y => B * (y : ℂ) ^ (B - 1) with hu'_def
  set v : ℝ → ℂ := fun y => (((1 + y : ℝ)) : ℂ) ^ (-b) * (((1 + x + y : ℝ)) : ℂ) ^ (-d) with hv_def
  set v' : ℝ → ℂ := fun y => (-b) * (((1 + y : ℝ)) : ℂ) ^ (-b - 1) * (((1 + x + y : ℝ)) : ℂ) ^ (-d) +
    (((1 + y : ℝ)) : ℂ) ^ (-b) * ((-d) * (((1 + x + y : ℝ)) : ℂ) ^ (-d - 1)) with hv'_def
  have hu : ∀ y ∈ Ioi (0:ℝ), HasDerivAt u (u' y) y := by
    intro y hy
    have hy' : (0:ℝ) < y := hy
    exact hasDerivAt_ofReal_cpow_const hy'.ne' hB0
  have hv : ∀ y ∈ Ioi (0:ℝ), HasDerivAt v (v' y) y := by
    intro y hy
    have hy' : (0:ℝ) < y := hy
    have e : v = fun t : ℝ => (1 + (t : ℂ)) ^ (-b) * (1 + (x : ℂ) + (t : ℂ)) ^ (-d) := by
      funext t; simp only [hv_def]; push_cast; ring_nf
    have s1 : (1 : ℂ) + (y : ℂ) ∈ slitPlane := by
      rw [show (1 : ℂ) + (y : ℂ) = ((1 + y : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.2 (by linarith)
    have s2 : (1 : ℂ) + (x : ℂ) + (y : ℂ) ∈ slitPlane := by
      rw [show (1 : ℂ) + (x : ℂ) + (y : ℂ) = ((1 + x + y : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.2 (by linarith)
    have h2 : HasDerivAt (fun z : ℂ => (1 + z) ^ (-b)) (-b * (1 + (y : ℂ)) ^ (-b - 1) * 1) (y : ℂ) :=
      ((hasDerivAt_id' (y : ℂ)).const_add 1).cpow_const s1
    have h3 : HasDerivAt (fun z : ℂ => (1 + (x : ℂ) + z) ^ (-d)) (-d * (1 + (x : ℂ) + (y : ℂ)) ^ (-d - 1) * 1)
        (y : ℂ) := ((hasDerivAt_id' (y : ℂ)).const_add (1 + (x : ℂ))).cpow_const s2
    have h23 := (h2.mul h3).comp_ofReal
    rw [e]
    refine h23.congr_deriv ?_
    simp only [hv'_def]; push_cast; ring

  have I0 : Integrable (kk B b d x) μ0 := integrable_kk B b d hB hd.le hlt hx.le
  have I1 : Integrable (kk (B + 1) (b + 1) d x) μ0 :=
    integrable_kk (B + 1) (b + 1) d (by simp; linarith) hd.le (by simp; linarith) hx.le
  have I2 : Integrable (kk (B + 1) b (d + 1) x) μ0 :=
    integrable_kk (B + 1) b (d + 1) (by simp; linarith) (by simp; linarith) (by simp; linarith) hx.le

  have hpt : ∀ y ∈ Ioi (0:ℝ), u' y * v y + u y * v' y
      = B * kk B b d x y - b * kk (B + 1) (b + 1) d x y - d * kk (B + 1) b (d + 1) x y := by
    intro y hy
    have hy' : (0:ℝ) < y := hy
    have hy1 : (0:ℝ) < 1 + y := by linarith
    have hy2 : (0:ℝ) < 1 + x + y := by linarith
    simp only [hu_def, hu'_def, hv_def, hv'_def, kk]
    have e1 : (y : ℂ) ^ B = (y : ℂ) ^ (B + 1 - 1) := by ring_nf
    have e2 : (((1 + y : ℝ)) : ℂ) ^ (-b - 1) = (((1 + y : ℝ)) : ℂ) ^ (-(b + 1)) := by ring_nf
    have e3 : (((1 + x + y : ℝ)) : ℂ) ^ (-d - 1) = (((1 + x + y : ℝ)) : ℂ) ^ (-(d + 1)) := by ring_nf
    rw [e2, e3, ← e1]
    ring
  have huv : IntegrableOn (u' * v + u * v') (Ioi (0:ℝ)) := by
    have h : Integrable (fun y => B * kk B b d x y - b * kk (B + 1) (b + 1) d x y - d * kk (B + 1) b (d + 1) x y) μ0 :=
      ((I0.const_mul B).sub (I1.const_mul b)).sub (I2.const_mul d)
    refine (IntegrableOn.congr_fun h (fun y hy => ?_) measurableSet_Ioi)
    simp only [Pi.add_apply, Pi.mul_apply]
    exact (hpt y hy).symm

  have hnorm : ∀ y : ℝ, 0 < y → ‖(u * v) y‖ = y ^ B.re * (1 + y) ^ (-b.re) * (1 + x + y) ^ (-d.re) := by
    intro y hy
    simp only [Pi.mul_apply, hu_def, hv_def, norm_mul, norm_ofReal_cpow hy]
    rw [norm_ofReal_cpow (by linarith), norm_ofReal_cpow (by linarith), neg_re, neg_re, mul_assoc]
  have h_zero : Tendsto (u * v) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun y : ℝ => y ^ B.re) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc := (Real.continuousAt_rpow_const 0 B.re (Or.inr hB.le)).tendsto
      rw [Real.zero_rpow hB.ne'] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' ?_ ?_ hlim
    · exact Eventually.of_forall fun y => norm_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : (0:ℝ) < y := hy
      rw [hnorm y hy']
      have h1 : (1 + y) ^ (-b.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      have h2 : (1 + x + y) ^ (-d.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      have h3 : 0 ≤ y ^ B.re := by positivity
      have h4 : 0 ≤ (1 + y) ^ (-b.re) := by positivity
      calc y ^ B.re * (1 + y) ^ (-b.re) * (1 + x + y) ^ (-d.re) ≤ y ^ B.re * 1 * 1 := by
            gcongr
        _ = y ^ B.re := by ring
  have h_infty : Tendsto (u * v) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun y : ℝ => y ^ (-(b.re + d.re - B.re))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    refine squeeze_zero' ?_ ?_ hlim
    · exact Eventually.of_forall fun y => norm_nonneg _
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
      rw [hnorm y hy]
      have h1 : (1 + y) ^ (-b.re) ≤ y ^ (-b.re) := Real.rpow_le_rpow_of_nonpos hy (by linarith) (by linarith)
      have h2 : (1 + x + y) ^ (-d.re) ≤ y ^ (-d.re) :=
        Real.rpow_le_rpow_of_nonpos hy (by linarith) (by linarith)
      have h3 : 0 ≤ y ^ B.re := by positivity
      have h4 : 0 ≤ (1 + y) ^ (-b.re) := by positivity
      calc y ^ B.re * (1 + y) ^ (-b.re) * (1 + x + y) ^ (-d.re) ≤ y ^ B.re * y ^ (-b.re) * y ^ (-d.re) := by
            gcongr
        _ = y ^ (-(b.re + d.re - B.re)) := by
            rw [← Real.rpow_add hy, ← Real.rpow_add hy]; congr 1; ring

  have key := integral_Ioi_deriv_mul_eq_sub hu hv huv h_zero h_infty
  have J1 : Integrable (fun y => B * kk B b d x y - b * kk (B + 1) (b + 1) d x y) μ0 :=
    (I0.const_mul B).sub (I1.const_mul b)
  rw [sub_zero, setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub J1 (I2.const_mul d),
    integral_sub (I0.const_mul B) (I1.const_mul b), integral_const_mul, integral_const_mul,
    integral_const_mul] at key
  exact key

theorem kk_split (B b d : ℂ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    kk (B + 1) b (d + 1) x y = kk B b d x y - (((1 + x : ℝ)) : ℂ) * kk B b (d + 1) x y := by
  have hy2 : (0:ℝ) < 1 + x + y := by linarith
  simp only [kk]
  have e1 : (y : ℂ) ^ (B + 1 - 1) = (y : ℂ) ^ (B - 1) * (y : ℂ) := by
    rw [mul_comm, ofReal_mul_cpow hy]; ring_nf
  have e2 : (((1 + x + y : ℝ)) : ℂ) ^ (-d) = (((1 + x + y : ℝ)) : ℂ) ^ (-(d + 1)) * (((1 + x + y : ℝ)) : ℂ) := by
    rw [mul_comm, ofReal_mul_cpow hy2]; ring_nf
  have e3 : (((1 + x + y : ℝ)) : ℂ) = (((1 + x : ℝ)) : ℂ) + (y : ℂ) := by push_cast; ring
  rw [e1, e2, e3]
  ring

theorem pointwise_J (a b D : ℂ) (ha : 0 < a.re) (hD : 0 < D.re) (hba : 0 < (b - a).re) {x : ℝ} (hx : 0 < x) :
    a * (∫ y in Ioi (0:ℝ), kk (a + D) b D x y) + D * ((((1 + x : ℝ)) : ℂ) * ∫ y in Ioi (0:ℝ), kk (a + D) b (D + 1) x y)
      = b * ∫ y in Ioi (0:ℝ), kk (a + D + 1) (b + 1) D x y := by
  have hbaR : a.re < b.re := by have := hba; simp at this; linarith
  have hb : 0 < b.re := by linarith
  have hB : 0 < (a + D).re := by simp; linarith
  have hlt : (a + D).re < b.re + D.re := by simp; linarith
  have h := ibp (a + D) b D hB hb hD hlt hx
  have I0 : Integrable (kk (a + D) b D x) μ0 := integrable_kk _ b D hB hD.le hlt hx.le
  have I2 : Integrable (kk (a + D) b (D + 1) x) μ0 :=
    integrable_kk _ b (D + 1) hB (by simp; linarith) (by simp; linarith) hx.le
  have hs : ∫ y in Ioi (0:ℝ), kk (a + D + 1) b (D + 1) x y
      = (∫ y in Ioi (0:ℝ), kk (a + D) b D x y) - (((1 + x : ℝ)) : ℂ) * ∫ y in Ioi (0:ℝ), kk (a + D) b (D + 1) x y := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => kk_split (a + D) b D hx hy),
      integral_sub I0 (I2.const_mul _), integral_const_mul]
  rw [hs] at h
  linear_combination h

def F (A a' β b' d : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (A - 1) * (((1 + x : ℝ)) : ℂ) ^ (-a') * ∫ y in Ioi (0:ℝ), kk β b' d x y

theorem measurable_F (A a' β b' d : ℂ) : Measurable (F A a' β b' d) := by
  unfold F
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · exact (Complex.measurable_ofReal.pow_const _)
  · exact (Complex.measurable_ofReal.comp (by fun_prop)).pow_const _
  · have h : StronglyMeasurable (Function.uncurry (kk β b' d)) := (measurable_kk β b' d).stronglyMeasurable
    exact (MeasureTheory.StronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioi (0:ℝ))) h).measurable

theorem F_eq (A a' β b' d : ℂ) (x : ℝ) :
    F A a' β b' d x = ∫ y in Ioi (0:ℝ), (x : ℂ) ^ (A - 1) * (((1 + x : ℝ)) : ℂ) ^ (-a') *
      ((y : ℂ) ^ (β - 1) * (((1 + y : ℝ)) : ℂ) ^ (-b')) * (((1 + x + y : ℝ)) : ℂ) ^ (-d) := by
  rw [F, ← integral_const_mul]
  congr 1; funext y; simp only [kk]; ring

theorem pointwise_F (A a b D : ℂ) (ha : 0 < a.re) (hD : 0 < D.re) (hba : 0 < (b - a).re) {x : ℝ} (hx : 0 < x) :
    a * F A (a + 1) (a + D) b D x + D * F A a (a + D) b (D + 1) x = b * F A (a + 1) (a + 1 + D) (b + 1) D x := by
  have hx1 : (0:ℝ) < 1 + x := by linarith
  have h := pointwise_J a b D ha hD hba hx
  simp only [F]
  have e1 : (((1 + x : ℝ)) : ℂ) ^ (-a) = (((1 + x : ℝ)) : ℂ) ^ (-(a + 1)) * (((1 + x : ℝ)) : ℂ) := by
    rw [mul_comm, ofReal_mul_cpow hx1]; ring_nf
  rw [e1, show a + 1 + D = a + D + 1 by ring]
  linear_combination ((x : ℂ) ^ (A - 1) * (((1 + x : ℝ)) : ℂ) ^ (-(a + 1))) * h

theorem integral_F_balanced (A a' b' d : ℂ) (hA : 0 < A.re) (hbA : 0 < (b' - A).re) (haD : 0 < (a' + d - A).re)
    (hba : 0 < (b' - a').re) :
    ∫ x in Ioi (0:ℝ), F A a' (a' + d) b' d x
      = Complex.Gamma A * Complex.Gamma (b' - A) * Complex.Gamma (a' + d - A) * Complex.Gamma (b' - a') /
          (Complex.Gamma b' * Complex.Gamma (d + b' - A)) := by
  rw [← Complex.integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance A a' b' d hA hbA
    haD hba]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  exact F_eq A a' (a' + d) b' d x

theorem integrable_F_balanced (A a' b' d : ℂ) (hA : 0 < A.re) (hbA : 0 < (b' - A).re) (haD : 0 < (a' + d - A).re)
    (hba : 0 < (b' - a').re) (hb : 0 < b'.re) (hden : 0 < (d + b' - A).re) :
    Integrable (F A a' (a' + d) b' d) μ0 := by
  by_contra hni
  have h0 := integral_undef hni
  have h1 := integral_F_balanced A a' b' d hA hbA haD hba
  rw [h0] at h1
  have hne : Complex.Gamma A * Complex.Gamma (b' - A) * Complex.Gamma (a' + d - A) * Complex.Gamma (b' - a') /
      (Complex.Gamma b' * Complex.Gamma (d + b' - A)) ≠ 0 := by
    refine div_ne_zero ?_ (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hb) (Complex.Gamma_ne_zero_of_re_pos hden))
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;> exact Complex.Gamma_ne_zero_of_re_pos ‹_›
  exact hne h1.symm

def FR (A a' β b' d : ℝ) (x : ℝ) : ℝ :=
  x ^ (A - 1) * (1 + x) ^ (-a') * ∫ y in Ioi (0:ℝ), kR β b' d x y

theorem F_ofReal (A a' β b' d : ℝ) {x : ℝ} (hx : 0 < x) :
    F (A : ℂ) (a' : ℂ) (β : ℂ) (b' : ℂ) (d : ℂ) x = ((FR A a' β b' d x : ℝ) : ℂ) := by
  simp only [F, FR]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => kk_ofReal β b' d hx.le hy), integral_complex_ofReal,
    show ((A : ℂ) - 1) = ((A - 1 : ℝ) : ℂ) by push_cast; ring, show (-(a' : ℂ)) = ((-a' : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow hx.le, ← ofReal_cpow (by linarith)]
  push_cast; ring

theorem FR_nonneg (A a' β b' d : ℝ) {x : ℝ} (hx : 0 < x) : 0 ≤ FR A a' β b' d x := by
  unfold FR
  have h : 0 ≤ ∫ y in Ioi (0:ℝ), kR β b' d x y :=
    setIntegral_nonneg measurableSet_Ioi fun y hy => kR_nonneg β b' d hx.le hy
  have : 0 < 1 + x := by linarith
  positivity

theorem norm_F_le (A a' β b' d : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖F A a' β b' d x‖ ≤ FR A.re a'.re β.re b'.re d.re x := by
  simp only [F, FR, norm_mul, norm_ofReal_cpow hx, sub_re, one_re]
  rw [norm_ofReal_cpow (by linarith), neg_re]
  have hx1 : 0 < 1 + x := by linarith
  have h0 : 0 ≤ x ^ (A.re - 1) * (1 + x) ^ (-a'.re) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h0
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  exact setIntegral_congr_fun measurableSet_Ioi (fun y hy => norm_kk β b' d hx.le hy)

theorem integrable_F_one (A a b D : ℂ) (hA : 0 < A.re) (ha : 0 < a.re) (hD : 0 < D.re) (hba : 0 < (b - a).re)
    (hbA : 0 < (b - A + 1).re) (haD : 0 < (a + D - A + 1).re) :
    Integrable (F A (a + 1) (a + D) b D) μ0 := by

  set Ar := A.re; set ar := a.re; set br := b.re; set Dr := D.re
  have hbaR : ar < br := by have := hba; simp at this; linarith
  have hbAR : 0 < br - Ar + 1 := by have := hbA; simp at this; linarith
  have haDR : 0 < ar + Dr - Ar + 1 := by have := haD; simp at this; linarith

  have hInt : Integrable (F (Ar : ℂ) ((ar : ℂ) + 1) ((ar : ℂ) + 1 + (Dr : ℂ)) ((br : ℂ) + 1) (Dr : ℂ)) μ0 :=
    integrable_F_balanced (Ar : ℂ) ((ar : ℂ) + 1) ((br : ℂ) + 1) (Dr : ℂ) (by simp; exact hA) (by simp; linarith)
      (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  have hIntR : Integrable (fun x => ((br / ar : ℝ)) * FR Ar (ar + 1) (ar + 1 + Dr) (br + 1) Dr x) μ0 := by
    refine (Integrable.congr hInt.norm ?_).const_mul _
    filter_upwards [ae_pos_μ0] with x hx
    rw [show ((ar : ℂ) + 1) = ((ar + 1 : ℝ) : ℂ) by push_cast; ring,
      show ((ar + 1 : ℝ) : ℂ) + (Dr : ℂ) = ((ar + 1 + Dr : ℝ) : ℂ) by push_cast; ring,
      show ((br : ℂ) + 1) = ((br + 1 : ℝ) : ℂ) by push_cast; ring, F_ofReal _ _ _ _ _ hx, norm_real,
      Real.norm_of_nonneg (FR_nonneg _ _ _ _ _ hx)]
  refine Integrable.mono' hIntR (measurable_F _ _ _ _ _).aestronglyMeasurable ?_
  filter_upwards [ae_pos_μ0] with x hx
  refine (norm_F_le _ _ _ _ _ hx).trans ?_

  have hP := pointwise_F (Ar : ℂ) (ar : ℂ) (br : ℂ) (Dr : ℂ) (by simp; exact ha) (by simp; exact hD)
    (by simp; linarith) hx
  rw [show ((ar : ℂ) + 1) = ((ar + 1 : ℝ) : ℂ) by push_cast; ring,
    show ((ar : ℂ) + (Dr : ℂ)) = ((ar + Dr : ℝ) : ℂ) by push_cast; ring,
    show ((Dr : ℂ) + 1) = ((Dr + 1 : ℝ) : ℂ) by push_cast; ring,
    show ((ar + 1 : ℝ) : ℂ) + (Dr : ℂ) = ((ar + 1 + Dr : ℝ) : ℂ) by push_cast; ring,
    show ((br : ℂ) + 1) = ((br + 1 : ℝ) : ℂ) by push_cast; ring,
    F_ofReal _ _ _ _ _ hx, F_ofReal _ _ _ _ _ hx, F_ofReal _ _ _ _ _ hx] at hP
  have hPR : ar * FR Ar (ar + 1) (ar + Dr) br Dr x + Dr * FR Ar ar (ar + Dr) br (Dr + 1) x
      = br * FR Ar (ar + 1) (ar + 1 + Dr) (br + 1) Dr x := by exact_mod_cast hP
  have h2 : 0 ≤ FR Ar ar (ar + Dr) br (Dr + 1) x := FR_nonneg _ _ _ _ _ hx
  have e : (a + 1).re = ar + 1 := by simp [ar]
  have e2 : (a + D).re = ar + Dr := by simp [ar, Dr]
  rw [e, e2]
  rw [show (br / ar : ℝ) * FR Ar (ar + 1) (ar + 1 + Dr) (br + 1) Dr x
      = (br * FR Ar (ar + 1) (ar + 1 + Dr) (br + 1) Dr x) / ar by ring, le_div_iff₀ ha, ← hPR]
  nlinarith [hD, h2]

theorem main (A a b D : ℂ) (hA : 0 < A.re) (ha : 0 < a.re) (hD : 0 < D.re) (hba : 0 < (b - a).re)
    (hbA : 0 < (b - A + 1).re) (haD : 0 < (a + D - A + 1).re) :
    a * (∫ x in Ioi (0:ℝ), F A (a + 1) (a + D) b D x) + D * (∫ x in Ioi (0:ℝ), F A a (a + D) b (D + 1) x)
      = Complex.Gamma A * Complex.Gamma (b - A + 1) * Complex.Gamma (a + D - A + 1) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A + 1)) := by
  have hbaR : a.re < b.re := by have := hba; simp at this; linarith
  have hb : 0 < b.re := by linarith
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  have I1 : Integrable (F A (a + 1) (a + D) b D) μ0 := integrable_F_one A a b D hA ha hD hba hbA haD
  have Ih : Integrable (F A (a + 1) (a + 1 + D) (b + 1) D) μ0 :=
    integrable_F_balanced A (a + 1) (b + 1) D hA (by simp at hbA ⊢; linarith) (by simp at haD ⊢; linarith)
      (by simp; linarith) (by simp; linarith) (by simp at hbA ⊢; linarith)
  have hval := integral_F_balanced A (a + 1) (b + 1) D hA (by simp at hbA ⊢; linarith) (by simp at haD ⊢; linarith)
    (by simp; linarith)

  have e2 : D * (∫ x in Ioi (0:ℝ), F A a (a + D) b (D + 1) x)
      = ∫ x in Ioi (0:ℝ), (b * F A (a + 1) (a + 1 + D) (b + 1) D x - a * F A (a + 1) (a + D) b D x) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have h := pointwise_F A a b D ha hD hba hx
    linear_combination h
  rw [e2, integral_sub (Ih.const_mul b) (I1.const_mul a), integral_const_mul, integral_const_mul, hval,
    show b + 1 - A = b - A + 1 by ring, show a + 1 + D - A = a + D - A + 1 by ring, show b + 1 - (a + 1) = b - a by ring,
    show D + (b + 1) - A = D + b - A + 1 by ring, Complex.Gamma_add_one b hb0]
  have hΓb : Complex.Gamma b ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hb
  have hΓq : Complex.Gamma (D + b - A + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp at hbA ⊢; linarith)
  field_simp
  ring

theorem main' (A a b D : ℂ) (hA : 0 < A.re) (ha : 0 < a.re) (hD : 0 < D.re) (hba : 0 < (b - a).re)
    (hbA : 0 < (b - A + 1).re) (haD : 0 < (a + D - A + 1).re) :
    a * (∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-(a + 1)) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-D)) +
    D * (∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-a) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-(D + 1)))
      = Complex.Gamma A * Complex.Gamma (b - A + 1) * Complex.Gamma (a + D - A + 1) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A + 1)) := by
  rw [← main A a b D hA ha hD hba hbA haD,
    setIntegral_congr_fun measurableSet_Ioi (fun x (hx : x ∈ Ioi (0:ℝ)) => (F_eq A (a + 1) (a + D) b D x)),
    setIntegral_congr_fun measurableSet_Ioi (fun x (hx : x ∈ Ioi (0:ℝ)) => (F_eq A a (a + D) b (D + 1) x))]

end P2mKcContig

end

theorem solution
    (A a b D : ℂ) (hA : 0 < A.re) (ha : 0 < a.re) (hD : 0 < D.re) (hba : 0 < (b - a).re)
    (hbA : 0 < (b - A + 1).re) (haD : 0 < (a + D - A + 1).re) :
    a * (∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-(a + 1)) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-D)) +
    D * (∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-a) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-(D + 1)))
      = Complex.Gamma A * Complex.Gamma (b - A + 1) * Complex.Gamma (a + D - A + 1) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A + 1)) :=
  P2mKcContig.main' A a b D hA ha hD hba hbA haD

end S_Complex_mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance
end P2MW
export P2MW.S_Complex_mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance (solution)
