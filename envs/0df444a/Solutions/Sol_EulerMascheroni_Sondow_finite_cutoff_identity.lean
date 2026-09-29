-- Prove2me | solution 1 for EulerMascheroni.Sondow.finite_cutoff_identity
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-14T10:55:00.646551+00:00
-- url     : https://prove2.me/submissions/38bdc812-0ccc-4d5b-804b-5552822b8c18

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_eulerMascheroni_sondowCutoff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Intervals

-- Source: Solutions.SondowRationalIntegral
section
open MeasureTheory Filter Set
open scoped Topology

namespace EulerMascheroni.Sondow

theorem rational_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (∫ t in Ioi (0:ℝ), 1/((t+a)*(t+b))) = Real.log (b/a)/(b-a) := by
  let F : ℝ → ℝ := fun t => Real.log ((t+a)/(t+b))/(b-a)
  have hd (t : ℝ) (ht : t ∈ Ici (0:ℝ)) :
      HasDerivAt F (1/((t+a)*(t+b))) t := by
    have hta : t+a ≠ 0 := by linarith [ht.out]
    have htb : t+b ≠ 0 := by linarith [ht.out]
    have hba : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
    have h := ((((hasDerivAt_id t).add_const a).div
      ((hasDerivAt_id t).add_const b) htb).log (div_ne_zero hta htb)).div_const (b-a)
    convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => (t+b)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ b tendsto_id)
    have hratio : (fun t : ℝ => 1+(a-b)*(t+b)⁻¹) =ᶠ[atTop]
        (fun t => (t+a)/(t+b)) := by
      filter_upwards [eventually_gt_atTop (-b)] with t ht
      field_simp [show t+b ≠ 0 by linarith]; ring
    have hh' := ((tendsto_const_nhds.add (hi.const_mul (a-b))).congr' hratio).log
      (by norm_num : (1:ℝ)+(a-b)*0 ≠ 0)
    simpa [F] using hh'.div_const (b-a)
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd
    (fun t ht => by
      have ht0 : 0 < t := ht
      positivity : ∀ t ∈ Ioi (0:ℝ), 0 ≤ 1/((t+a)*(t+b))) hlim
  change (∫ t in Ioi (0:ℝ), 1/((t+a)*(t+b))) = _ at he
  rw [he]
  simp only [F, zero_add]
  rw [Real.log_div hb.ne' ha.ne', Real.log_div ha.ne' hb.ne']
  ring

theorem rational_integral_diagonal (a : ℝ) (ha : 0 < a) :
    (∫ t in Ioi (0:ℝ), 1/((t+a)*(t+a))) = 1/a := by
  let F : ℝ → ℝ := fun t => -(t+a)⁻¹
  have hd (t : ℝ) (ht : t ∈ Ici (0:ℝ)) :
      HasDerivAt F (1/((t+a)*(t+a))) t := by
    have hta : t+a ≠ 0 := by linarith [ht.out]
    have h := (((hasDerivAt_id t).add_const a).inv hta).neg
    convert h using 1 <;> first | rfl | (dsimp; field_simp)
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa [F] using (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ a tendsto_id)).neg
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd
    (fun t ht => by
      have ht0 : 0 < t := ht
      positivity : ∀ t ∈ Ioi (0:ℝ), 0 ≤ 1/((t+a)*(t+a))) hlim
  simpa [F, one_div] using he

/-- Laplace representation of the reciprocal logarithm on the open unit interval. -/
theorem reciprocal_log_integral (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
    (∫ t in Ioi (0:ℝ), z ^ t) = 1 / (-Real.log z) := by
  have hl : Real.log z < 0 := Real.log_neg hz hz1
  have he := integral_exp_mul_Ioi hl 0
  simpa [Real.rpow_def_of_pos hz, div_eq_mul_inv] using he

theorem reciprocal_log_integrable (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
    IntegrableOn (fun t : ℝ => z ^ t) (Ioi (0:ℝ)) := by
  simpa [Real.rpow_def_of_pos hz] using
    integrableOn_exp_mul_Ioi (Real.log_neg hz hz1) 0

/-- Integrability is recovered from the nonzero evaluated integral, using Lean's
totalized Bochner integral convention. No integrability hypothesis is hidden. -/
theorem rational_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => 1/((t+a)*(t+b))) (Ioi (0:ℝ)) := by
  by_contra hi
  have hz := integral_undef hi
  by_cases hab : a = b
  · subst b
    rw [rational_integral_diagonal a ha] at hz
    exact (div_ne_zero one_ne_zero ha.ne') hz
  · rw [rational_integral a b ha hb hab] at hz
    have hr : b/a ≠ 1 := by
      intro he
      have : b = a := (div_eq_one_iff_eq ha.ne').mp he
      exact hab this.symm
    exact (div_ne_zero (Real.log_ne_zero_of_pos_of_ne_one (div_pos hb ha) hr)
      (sub_ne_zero.mpr (Ne.symm hab))) hz

/-- The one-dimensional moments used after introducing the Laplace parameter. -/
theorem unit_rpow_integral (r : ℝ) (hr : -1 < r) :
    (∫ x in (0:ℝ)..1, x ^ r) = 1/(r+1) := by
  simpa [Real.zero_rpow (show r+1 ≠ 0 by linarith)] using
    integral_rpow (a := (0:ℝ)) (b := 1) (Or.inl hr)

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowLogMoment
section
open MeasureTheory Filter Set
open scoped Topology

namespace EulerMascheroni.Sondow

private noncomputable abbrev unitMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

private theorem unit_rpow_set_integral (r : ℝ) (hr : -1 < r) :
    (∫ x, x ^ r ∂unitMeasure) = 1/(r+1) := by
  rw [← unit_rpow_integral r hr, intervalIntegral.integral_of_le (by norm_num)]

private theorem unit_rpow_integrable (r : ℝ) (hr : -1 < r) :
    Integrable (fun x : ℝ => x ^ r) unitMeasure :=
  (intervalIntegral.intervalIntegrable_rpow' hr).1

private theorem parameter_moment (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 < t) :
    (∫ p : ℝ × ℝ, p.1 ^ (a+t) * p.2 ^ (b+t) ∂unitMeasure.prod unitMeasure) =
      1/((t+(a+1))*(t+(b+1))) := by
  rw [integral_prod_mul (fun x : ℝ => x ^ (a+t)) (fun y : ℝ => y ^ (b+t)),
    unit_rpow_set_integral _ (by linarith),
    unit_rpow_set_integral _ (by linarith)]
  rw [← one_div_mul_one_div]
  congr 2 <;> ring

/-- Absolute integrability needed for exchanging the Laplace parameter and the square. -/
theorem logarithmic_moment_parameter_integrable (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => q.2.1 ^ (a+q.1) * q.2.2 ^ (b+q.1))
      ((volume.restrict (Ioi 0)).prod (unitMeasure.prod unitMeasure)) := by
  apply (integrable_prod_iff (by fun_prop)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (unit_rpow_integrable (a+t) (by linarith [ht.out])).mul_prod
      (unit_rpow_integrable (b+t) (by linarith [ht.out]))
  · apply (rational_integrable (a+1) (b+1) (by linarith) (by linarith)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [← parameter_moment a b t ha hb ht]
    apply integral_congr_ae
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact (Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.1.le _)
      (Real.rpow_nonneg hy.1.le _))).symm

private theorem pointwise_laplace_moment (a b x y : ℝ)
    (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    (∫ t in Ioi (0:ℝ), x ^ (a+t) * y ^ (b+t)) =
      x ^ a * y ^ b / (-Real.log (x*y)) := by
  have hxy : x*y < 1 := by nlinarith [hx.2, mul_pos hx.1 (sub_pos.mpr hy.2)]
  calc
    _ = ∫ t in Ioi (0:ℝ), (x ^ a * y ^ b) * (x*y) ^ t := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        dsimp only
        rw [Real.rpow_add hx.1, Real.rpow_add hy.1, Real.mul_rpow hx.1.le hy.1.le]
        ring)
    _ = _ := by
      rw [integral_const_mul, reciprocal_log_integral (x*y) (mul_pos hx.1 hy.1) hxy]
      ring

private theorem laplace_moment_ae (a b : ℝ) :
    (fun p : ℝ × ℝ => ∫ t in Ioi (0:ℝ), p.1 ^ (a+t) * p.2 ^ (b+t))
      =ᵐ[unitMeasure.prod unitMeasure]
        (fun p => p.1 ^ a * p.2 ^ b / (-Real.log (p.1*p.2))) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => ∫ t in Ioi (0:ℝ),
      p.1 ^ (a+t) * p.2 ^ (b+t)) :=
    (show StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      q.1.1 ^ (a+q.2) * q.1.2 ^ (b+q.2)) from by fun_prop).integral_prod_right'.measurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hmeas (by fun_prop))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with x hx hx1
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with y hy hy1
  exact pointwise_laplace_moment a b x y ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩

theorem logarithmic_moment_integrable (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ a * p.2 ^ b / (-Real.log (p.1*p.2)))
      ((volume.restrict (Ioc 0 1)).prod (volume.restrict (Ioc 0 1))) :=
  (logarithmic_moment_parameter_integrable a b ha hb).integral_prod_right.congr
    (laplace_moment_ae a b)

/-- The elementary double logarithmic moment reduced to a rational improper integral. -/
theorem logarithmic_moment_eq_rational (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ a * y ^ b / (-Real.log (x*y))) =
      ∫ t in Ioi (0:ℝ), 1/((t+(a+1))*(t+(b+1))) := by
  have hi := logarithmic_moment_parameter_integrable a b ha hb
  have hs := integral_integral_swap
    (f := fun (t : ℝ) (p : ℝ × ℝ) => p.1 ^ (a+t) * p.2 ^ (b+t)) hi
  have hp : (∫ t in Ioi (0:ℝ), ∫ p : ℝ × ℝ,
      p.1 ^ (a+t) * p.2 ^ (b+t) ∂unitMeasure.prod unitMeasure) =
      ∫ t in Ioi (0:ℝ), 1/((t+(a+1))*(t+(b+1))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact parameter_moment a b t ha hb ht
  have he : (fun p : ℝ × ℝ => ∫ t in Ioi (0:ℝ),
      p.1 ^ (a+t) * p.2 ^ (b+t)) =ᵐ[unitMeasure.prod unitMeasure]
      (fun p => p.1 ^ a * p.2 ^ b / (-Real.log (p.1*p.2))) := laplace_moment_ae a b
  have hm : Integrable (fun p : ℝ × ℝ => p.1 ^ a * p.2 ^ b / (-Real.log (p.1*p.2)))
      (unitMeasure.prod unitMeasure) := hi.integral_prod_right.congr he
  rw [integral_congr_ae he] at hs
  rw [← hp, hs, integral_prod _ hm]
  simp only [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]

theorem logarithmic_moment_diagonal (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ a * y ^ a / (-Real.log (x*y))) = 1/(a+1) := by
  rw [logarithmic_moment_eq_rational a a ha ha,
    rational_integral_diagonal (a+1) (by linarith)]

theorem logarithmic_moment_off_diagonal (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≠ b) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ a * y ^ b / (-Real.log (x*y))) = Real.log ((b+1)/(a+1))/(b-a) := by
  rw [logarithmic_moment_eq_rational a b ha hb,
    rational_integral (a+1) (b+1) (by linarith) (by linarith) (by simpa)]
  congr 1
  ring

theorem logarithmic_nat_moment_diagonal (a : ℕ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ a * y ^ a / (-Real.log (x*y))) = 1/(a+1:ℝ) := by
  simpa using logarithmic_moment_diagonal (a:ℝ) (by positivity)

theorem logarithmic_nat_moment_off_diagonal (a b : ℕ) (hab : a ≠ b) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ a * y ^ b / (-Real.log (x*y))) = Real.log ((b+1:ℝ)/(a+1:ℝ))/((b:ℝ)-a) := by
  simpa using logarithmic_moment_off_diagonal (a:ℝ) (b:ℝ) (by positivity)
    (by positivity) (by exact_mod_cast hab)

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowKernelExpansion
section
open Finset

namespace EulerMascheroni.Sondow

theorem weighted_binomial_expansion (n : ℕ) (x : ℝ) :
    (x*(1-x))^n = ∑ i ∈ range (n+1),
      ((-1:ℝ)^i*(n.choose i:ℝ)) * x^(n+i) := by
  rw [mul_pow, show 1-x = -x+1 by ring, add_pow, mul_sum]
  apply sum_congr rfl
  intro i hi
  simp only [one_pow, mul_one, pow_add]
  rw [neg_pow]
  ring

theorem numerator_expansion (n : ℕ) (x y : ℝ) :
    (x*(1-x)*y*(1-y))^n =
      ∑ i ∈ range (n+1), ∑ j ∈ range (n+1),
        ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) *
          (x^(n+i)*y^(n+j)) := by
  rw [show x*(1-x)*y*(1-y) = (x*(1-x))*(y*(1-y)) by ring,
    mul_pow, weighted_binomial_expansion, weighted_binomial_expansion, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- Exact pointwise finite expansion away from the geometric pole. -/
theorem truncated_kernel_expansion (n N : ℕ) (x y : ℝ) (hxy : x*y ≠ 1) :
    (x*(1-x)*y*(1-y))^n / ((1-x*y)*(-Real.log (x*y))) * (1-(x*y)^N) =
      ∑ i ∈ range (n+1), ∑ j ∈ range (n+1), ∑ v ∈ range N,
        ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) *
          (x^(n+i+v)*y^(n+j+v)/(-Real.log (x*y))) := by
  rw [← geom_sum_mul_neg (x*y) N]
  have hden : 1-x*y ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  rw [show (x*(1-x)*y*(1-y))^n / ((1-x*y)*(-Real.log (x*y))) *
      ((∑ v ∈ range N, (x*y)^v)*(1-x*y)) =
      (x*(1-x)*y*(1-y))^n * (∑ v ∈ range N, (x*y)^v) / (-Real.log (x*y)) by
        field_simp]
  rw [numerator_expansion, sum_mul, sum_div]
  apply sum_congr rfl
  intro i hi
  rw [sum_mul, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [mul_sum, sum_div]
  apply sum_congr rfl
  intro v hv
  simp only [pow_add, mul_pow]
  ring

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowTruncatedIntegral
section
open MeasureTheory Filter Set
open Finset (range)

namespace EulerMascheroni.Sondow

noncomputable abbrev squareMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc 0 1)).prod (volume.restrict (Ioc 0 1))

theorem ae_open_square : ∀ᵐ p ∂squareMeasure, p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with x hx hx1
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with y hy hy1
  exact ⟨⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩, ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩⟩

noncomputable def integralKernel (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  (p.1*(1-p.1)*p.2*(1-p.2))^n / ((1-p.1*p.2)*(-Real.log (p.1*p.2)))

theorem integralKernel_bound (n : ℕ) (hn : 0 < n) (p : ℝ × ℝ)
    (hp : p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo 0 1) :
    0 ≤ integralKernel n p ∧ integralKernel n p ≤ 1/(-Real.log (p.1*p.2)) := by
  obtain ⟨hx, hy⟩ := hp
  have ht : 0 < p.1*p.2 := mul_pos hx.1 hy.1
  have ht1 : p.1*p.2 < 1 := by nlinarith [hx.2, mul_pos hx.1 (sub_pos.mpr hy.2)]
  have hl : 0 < -Real.log (p.1*p.2) := neg_pos.mpr (Real.log_neg ht ht1)
  have hu : 0 ≤ p.1*(1-p.1)*p.2*(1-p.2) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hx.1.le (by linarith [hx.2])) hy.1.le)
      (by linarith [hy.2])
  have hu1 : p.1*(1-p.1)*p.2*(1-p.2) ≤ 1-p.1*p.2 := by
    have hprod : (1-p.1)*(1-p.2) ≤ 1-p.1*p.2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1.le,
        mul_nonneg (sub_nonneg.mpr hy.2.le) hx.1.le]
    have hh := mul_le_mul_of_nonneg_right ht1.le
      (mul_nonneg (sub_nonneg.mpr hx.2.le) (sub_nonneg.mpr hy.2.le))
    nlinarith
  have hpow : (p.1*(1-p.1)*p.2*(1-p.2))^n ≤ 1-p.1*p.2 := by
    exact (pow_le_of_le_one hu (by linarith) hn.ne').trans hu1
  unfold integralKernel
  refine ⟨div_nonneg (pow_nonneg hu _) (by positivity), ?_⟩
  apply (div_le_iff₀ (mul_pos (sub_pos.mpr ht1) hl)).mpr
  calc
    _ ≤ 1-p.1*p.2 := hpow
    _ = _ := by field_simp [neg_ne_zero.mp hl.ne']

theorem integralKernel_integrable (n : ℕ) (hn : 0 < n) :
    Integrable (integralKernel n) squareMeasure := by
  have hbase : Integrable (fun p : ℝ × ℝ => 1/(-Real.log (p.1*p.2))) squareMeasure := by
    simpa using logarithmic_moment_integrable 0 0 (by norm_num) (by norm_num)
  apply hbase.mono' (show Measurable (integralKernel n) from by
    unfold integralKernel; fun_prop).aestronglyMeasurable
  filter_upwards [ae_open_square] with p hp
  obtain ⟨hpos, hbound⟩ := integralKernel_bound n hn p hp
  simpa [Real.norm_of_nonneg hpos] using hbound

theorem cutoffKernel_integrable (n N : ℕ) (hn : 0 < n) :
    Integrable (fun p => integralKernel n p * (p.1*p.2)^N) squareMeasure := by
  apply (integralKernel_integrable n hn).mono'
    (show Measurable (fun p => integralKernel n p * (p.1*p.2)^N) from by
      unfold integralKernel; fun_prop).aestronglyMeasurable
  filter_upwards [ae_open_square] with p hp
  have hpos := (integralKernel_bound n hn p hp).1
  have ht : 0 ≤ p.1*p.2 := mul_nonneg hp.1.1.le hp.2.1.le
  have ht1 : p.1*p.2 ≤ 1 := by
    nlinarith [hp.1.2, mul_pos hp.1.1 (sub_pos.mpr hp.2.2)]
  rw [Real.norm_of_nonneg (mul_nonneg hpos (pow_nonneg ht _))]
  exact mul_le_of_le_one_right hpos (pow_le_one₀ ht ht1)

theorem I_eq_square_integral (n : ℕ) (hn : 0 < n) :
    I n = ∫ p, integralKernel n p ∂squareMeasure := by
  rw [integral_prod _ (integralKernel_integrable n hn)]
  simp only [I, integralKernel, intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]

theorem remainder_eq_square_integral (n N : ℕ) (hn : 0 < n) :
    remainder n N = ∫ p, integralKernel n p * (p.1*p.2)^N ∂squareMeasure := by
  rw [integral_prod _ (cutoffKernel_integrable n N hn)]
  simp only [remainder, integralKernel,
    intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]

theorem nat_moment_integrable (a b : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1^a*p.2^b/(-Real.log (p.1*p.2))) squareMeasure := by
  simpa using logarithmic_moment_integrable (a:ℝ) (b:ℝ) (by positivity) (by positivity)

theorem truncated_integral_moment_expansion (n N : ℕ) (hn : 0 < n) :
    I n - remainder n N =
      ∑ i ∈ range (n+1), ∑ j ∈ range (n+1), ∑ v ∈ range N,
        ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) *
          (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
            x^(n+i+v)*y^(n+j+v)/(-Real.log (x*y))) := by
  let F (i j v : ℕ) (p : ℝ × ℝ) : ℝ :=
    ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) *
      (p.1^(n+i+v)*p.2^(n+j+v)/(-Real.log (p.1*p.2)))
  have hF (i j v : ℕ) : Integrable (F i j v) squareMeasure :=
    (nat_moment_integrable (n+i+v) (n+j+v)).const_mul _
  rw [I_eq_square_integral n hn, remainder_eq_square_integral n N hn,
    ← integral_sub (integralKernel_integrable n hn) (cutoffKernel_integrable n N hn)]
  have he : (fun p => integralKernel n p - integralKernel n p * (p.1*p.2)^N)
      =ᵐ[squareMeasure] (fun p => ∑ i ∈ range (n+1), ∑ j ∈ range (n+1),
        ∑ v ∈ range N, F i j v p) := by
    filter_upwards [ae_open_square] with p hp
    have ht1 : p.1*p.2 < 1 := by
      nlinarith [hp.1.2, mul_pos hp.1.1 (sub_pos.mpr hp.2.2)]
    simpa only [F, integralKernel, mul_sub, mul_one] using
      truncated_kernel_expansion n N p.1 p.2 ht1.ne
  rw [integral_congr_ae he, integral_finsetSum _ (fun i hi =>
    integrable_finsetSum _ (fun j hj => integrable_finsetSum _ (fun v hv => hF i j v)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j hj => integrable_finsetSum _ (fun v hv => hF i j v))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum _ (fun v hv => hF i j v)]
  apply Finset.sum_congr rfl
  intro v hv
  dsimp only [F]
  rw [integral_const_mul, integral_prod _ (nat_moment_integrable (n+i+v) (n+j+v))]
  simp only [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowFiniteSums
section
open Finset

namespace EulerMascheroni.Sondow

/-- Diagonal moment summation, including the empty cutoff. -/
theorem harmonic_moment_sum (m N : ℕ) :
    (∑ v ∈ range N, (1:ℝ)/(m+v+1:ℕ)) =
      (harmonic (m+N):ℝ) - (harmonic m:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, show m+(N+1) = (m+N)+1 by omega, harmonic_succ]
    push_cast
    ring

/-- Discrete rectangle telescoping: sum the same boundary in the two directions. -/
theorem rectangular_sum_difference (f : ℕ → ℝ) (N d : ℕ) :
    (∑ v ∈ range N, (f (v+d)-f v)) =
      ∑ k ∈ range d, (f (N+k)-f k) := by
  have h1 := sum_range_add f N d
  have h2 := sum_range_add f d N
  rw [Nat.add_comm d N] at h2
  simp_rw [sum_sub_distrib]
  have he : (∑ v ∈ range N, f (d+v)) = ∑ v ∈ range N, f (v+d) := by
    apply sum_congr rfl
    intro v hv
    rw [Nat.add_comm]
  rw [he] at h2
  linarith

/-- Off-diagonal moments telescope to the short boundary logarithmic sum. -/
theorem logarithmic_moment_sum (m N d : ℕ) :
    (∑ v ∈ range N, Real.log ((m+v+d+1:ℕ)/(m+v+1:ℝ))) =
      ∑ k ∈ range d, Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ)) := by
  have he := rectangular_sum_difference (fun v => Real.log (m+v+1:ℕ)) N d
  have hl (v : ℕ) :
      Real.log ((m+v+d+1:ℕ)/(m+v+1:ℝ)) =
        Real.log (m+(v+d)+1:ℕ) - Real.log (m+v+1:ℕ) := by
    rw [Real.log_div (by positivity) (by positivity)]
    push_cast
    congr 1; congr 1; ring
  have hr (k : ℕ) :
      Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ)) =
        Real.log (m+(N+k)+1:ℕ) - Real.log (m+k+1:ℕ) := by
    rw [Real.log_div (by positivity) (by positivity)]
    push_cast
    congr 1; congr 1; ring
  simp_rw [hl, hr]
  exact he

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowFiniteMoments
section
open MeasureTheory Finset

namespace EulerMascheroni.Sondow

/-- Evaluation of the diagonal in the finite geometric expansion. -/
theorem finite_diagonal_moments (m N : ℕ) :
    (∑ v ∈ range N, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ (m+v) * y ^ (m+v) / (-Real.log (x*y))) =
      (harmonic (m+N):ℝ) - (harmonic m:ℝ) := by
  simp_rw [logarithmic_nat_moment_diagonal]
  simpa only [Nat.cast_add, Nat.cast_one] using harmonic_moment_sum m N

/-- Evaluation of an off-diagonal in the finite geometric expansion. -/
theorem finite_off_diagonal_moments (m N d : ℕ) (hd : 0 < d) :
    (∑ v ∈ range N, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ (m+v) * y ^ (m+v+d) / (-Real.log (x*y))) =
      (∑ k ∈ range d, Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ))) / (d:ℝ) := by
  calc
    _ = ∑ v ∈ range N, Real.log ((m+v+d+1:ℕ)/(m+v+1:ℝ))/(d:ℝ) := by
      apply sum_congr rfl
      intro v hv
      rw [logarithmic_nat_moment_off_diagonal _ _ (by omega)]
      push_cast
      congr 1
      ring
    _ = _ := by rw [← sum_div, logarithmic_moment_sum]

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowSymmetricSums
section
open Finset

namespace EulerMascheroni.Sondow

/-- Pair the strict lower and upper triangles of a symmetric finite matrix. -/
theorem symmetric_square_sum (f : ℕ → ℕ → ℝ) (hsymm : ∀ i j, f i j = f j i) (m : ℕ) :
    (∑ i ∈ range m, ∑ j ∈ range m, f i j) =
      (∑ i ∈ range m, f i i) + 2 * ∑ j ∈ range m, ∑ i ∈ range j, f i j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : (∑ i ∈ range (m+1), ∑ j ∈ range (m+1), f i j) =
        (∑ i ∈ range m, ∑ j ∈ range m, f i j) +
          (∑ i ∈ range m, f i m) + (∑ j ∈ range m, f m j) + f m m := by
      rw [sum_range_succ]
      simp_rw [sum_range_succ]
      rw [sum_add_distrib]
      ring
    have he : (∑ j ∈ range m, f m j) = ∑ i ∈ range m, f i m := by
      apply sum_congr rfl
      intro i hi
      exact hsymm m i
    rw [hsplit, ih, he, sum_range_succ, sum_range_succ]
    ring

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowFiniteEvaluation
section
open MeasureTheory Finset

namespace EulerMascheroni.Sondow

theorem nat_moment_symmetric (a b : ℕ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, x^a*y^b/(-Real.log (x*y))) =
      ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, x^b*y^a/(-Real.log (x*y)) := by
  simp_rw [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  rw [integral_integral_swap (f := fun x y : ℝ => x^a*y^b/(-Real.log (x*y)))
    (nat_moment_integrable a b)]
  congr 1
  funext x
  congr 1
  funext y
  rw [mul_comm y x, mul_comm (y^a) (x^b)]

/-- The truncated integral evaluated into harmonic numbers and finite logarithmic sums.
The remaining identification with L is a finite combinatorial identity. -/
theorem finite_cutoff_evaluation (n N : ℕ) (hn : 0 < n) :
    I n - remainder n N =
      (∑ i ∈ range (n+1), (n.choose i:ℝ)^2 *
        ((harmonic (n+i+N):ℝ)-(harmonic (n+i):ℝ))) +
      2 * ∑ j ∈ range (n+1), ∑ i ∈ range j,
        ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ) *
          ∑ k ∈ range (j-i), Real.log ((n+i+N+k+1:ℕ)/(n+i+k+1:ℝ)) := by
  let F (i j : ℕ) : ℝ :=
    ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) *
      ∑ v ∈ range N, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        x^(n+i+v)*y^(n+j+v)/(-Real.log (x*y))
  have hsymm (i j : ℕ) : F i j = F j i := by
    dsimp only [F]
    have he : (∑ v ∈ range N, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        x^(n+i+v)*y^(n+j+v)/(-Real.log (x*y))) =
      ∑ v ∈ range N, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        x^(n+j+v)*y^(n+i+v)/(-Real.log (x*y)) := by
      apply sum_congr rfl
      intro v hv
      exact nat_moment_symmetric _ _
    rw [he, Nat.add_comm i j]
    ring
  have hexp : I n - remainder n N = ∑ i ∈ range (n+1), ∑ j ∈ range (n+1), F i j := by
    rw [truncated_integral_moment_expansion n N hn]
    simp only [F, mul_sum]
  rw [hexp, symmetric_square_sum F hsymm]
  congr 1
  · apply sum_congr rfl
    intro i hi
    dsimp only [F]
    rw [finite_diagonal_moments]
    have hsign : (-1:ℝ)^(i+i) = 1 := by
      rw [← two_mul i, pow_mul]
      norm_num
    rw [hsign]
    ring
  · congr 1
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro i hi
    have hij : i < j := mem_range.mp hi
    dsimp only [F]
    have hindex (v : ℕ) : n+j+v = (n+i)+v+(j-i) := by omega
    simp_rw [hindex]
    rw [finite_off_diagonal_moments (n+i) N (j-i) (by omega)]
    push_cast
    ring

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowBinomialCoefficients
section
open Finset

namespace EulerMascheroni.Sondow

theorem signed_choose_sum (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ range (n+1), (-1:ℝ)^i*(n.choose i:ℝ)) = 0 := by
  exact_mod_cast Int.alternating_sum_range_choose_of_ne hn.ne'

theorem choose_square_sum (n : ℕ) :
    (∑ i ∈ range (n+1), (n.choose i:ℝ)^2) = ((2*n).choose n:ℝ) := by
  exact_mod_cast Nat.sum_range_choose_sq n

/-- Coefficient of log N after pairing the off-diagonal moments. -/
theorem signed_triangular_choose_sum (n : ℕ) (hn : 0 < n) :
    2 * (∑ j ∈ range (n+1), ∑ i ∈ range j,
      (-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) = -((2*n).choose n:ℝ) := by
  let c (i : ℕ) : ℝ := (-1:ℝ)^i*(n.choose i:ℝ)
  have hs : (∑ i ∈ range (n+1), ∑ j ∈ range (n+1), c i*c j) = 0 := by
    simp_rw [← mul_sum]
    change (∑ i ∈ range (n+1), c i *
      (∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ))) = 0
    rw [signed_choose_sum n hn]
    simp
  have hd : (∑ i ∈ range (n+1), c i*c i) = ((2*n).choose n:ℝ) := by
    rw [← choose_square_sum]
    apply sum_congr rfl
    intro i hi
    have he : (-1:ℝ)^i * (-1:ℝ)^i = 1 := by
      rw [← pow_add, ← two_mul i, pow_mul]
      norm_num
    dsimp only [c]
    nlinarith [he]
  have he := symmetric_square_sum (fun i j => c i*c j) (fun i j => mul_comm _ _) (n+1)
  rw [hs, hd] at he
  have ht : (∑ j ∈ range (n+1), ∑ i ∈ range j, c i*c j) =
      ∑ j ∈ range (n+1), ∑ i ∈ range j,
        (-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ) := by
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro i hi
    dsimp only [c]
    rw [pow_add]
    ring
  rw [ht] at he
  linarith

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowCutoffAlgebra
section
open Finset

namespace EulerMascheroni.Sondow

theorem triangular_sum_reindex (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range (n+1), ∑ i ∈ range j, f i j) =
      ∑ i ∈ range (n+1), ∑ j ∈ Icc (i+1) n, f i j := by
  have hI (i : ℕ) : Ico (i+1) (n+1) = Icc (i+1) n := by
    ext k
    simp only [mem_Ico, mem_Icc]
    omega
  simpa only [Nat.Ico_zero_eq_range, hI] using
    (sum_Ico_Ico_comm' 0 (n+1) f).symm

theorem range_sum_shift_one (f : ℕ → ℝ) (d : ℕ) :
    (∑ k ∈ range d, f (k+1)) = ∑ k ∈ Icc 1 d, f k := by
  have hI : Icc 1 d = Ico 1 (d+1) := by
    ext k
    simp only [mem_Ico, mem_Icc]
    omega
  rw [hI, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

theorem boundary_log_split (m N d : ℕ) (hN : 0 < N) :
    (∑ k ∈ range d, Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ))) =
      (d:ℝ)*Real.log N - (∑ k ∈ range d, Real.log (m+k+1:ℕ)) +
        ∑ k ∈ range d, Real.log (1+(m+k+1:ℕ)/(N:ℝ)) := by
  have he (k : ℕ) : Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ)) =
      Real.log N - Real.log (m+k+1:ℕ) + Real.log (1+(m+k+1:ℕ)/(N:ℝ)) := by
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    rw [Real.log_div (by positivity) (by positivity)]
    have hnum : (m+N+k+1:ℕ) = (N:ℝ)*(1+(m+k+1:ℕ)/(N:ℝ)) := by
      push_cast
      field_simp
      ring
    rw [hnum, Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  simp_rw [he, sum_add_distrib, sum_sub_distrib]
  simp

noncomputable def signedLogForm (n : ℕ) : ℝ :=
  -2 * ∑ j ∈ range (n+1), ∑ i ∈ range j,
    ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ) *
      ∑ k ∈ range (j-i), Real.log (n+i+k+1:ℕ)

theorem diagonal_cutoff_split (n N : ℕ) :
    (∑ i ∈ range (n+1), (n.choose i:ℝ)^2 *
      ((harmonic (n+i+N):ℝ)-(harmonic (n+i):ℝ))) =
      ((2*n).choose n:ℝ)*(harmonic N:ℝ) - (A n:ℝ) +
        ∑ i ∈ range (n+1), (n.choose i:ℝ)^2 *
          ((harmonic (N+n+i):ℝ)-(harmonic N:ℝ)) := by
  have hA : (A n:ℝ) = ∑ i ∈ range (n+1), (n.choose i:ℝ)^2*(harmonic (n+i):ℝ) := by
    simp only [A]
    push_cast
    rfl
  rw [hA, ← choose_square_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  rw [show n+i+N = N+n+i by omega]
  ring

theorem weighted_boundary_log_split (m N d : ℕ) (hN : 0 < N) (hd : 0 < d) (c : ℝ) :
    c/(d:ℝ) * (∑ k ∈ range d, Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ))) =
      c*Real.log N - c/(d:ℝ)*(∑ k ∈ range d, Real.log (m+k+1:ℕ)) +
        c/(d:ℝ)*(∑ k ∈ range d, Real.log (1+(m+k+1:ℕ)/(N:ℝ))) := by
  rw [boundary_log_split m N d hN]
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem correction_triangle_eq (n N : ℕ) :
    (∑ j ∈ range (n+1), ∑ i ∈ range j,
      ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ) *
        ∑ k ∈ range (j-i), Real.log (1+(n+i+k+1:ℕ)/(N:ℝ))) =
      ∑ i ∈ range (n+1), ∑ j ∈ Icc (i+1) n,
        ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ) *
          ∑ k ∈ Icc 1 (j-i), Real.log (1+(n+i+k:ℕ)/(N:ℝ)) := by
  rw [triangular_sum_reindex]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  congr 1
  simpa only [Nat.add_assoc] using range_sum_shift_one
    (fun k => Real.log (1+(n+i+k:ℕ)/(N:ℝ))) (j-i)

/-- Complete finite cutoff identity with the signed logarithmic form.
Identifying signedLogForm with L is the remaining combinatorial step. -/
theorem finite_cutoff_signed_identity (n N : ℕ) (hn : 0 < n) (hN : 0 < N) :
    I n - remainder n N = ((2*n).choose n:ℝ) *
      ((harmonic N:ℝ)-Real.log N) + signedLogForm n - (A n:ℝ) + cutoffError n N := by
  let c (i j : ℕ) : ℝ := (-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)
  let B (i j : ℕ) : ℝ := ∑ k ∈ range (j-i), Real.log (n+i+k+1:ℕ)
  let E (i j : ℕ) : ℝ := ∑ k ∈ range (j-i), Real.log (1+(n+i+k+1:ℕ)/(N:ℝ))
  have hcoeff : 2*(∑ j ∈ range (n+1), ∑ i ∈ range j, c i j) =
      -((2*n).choose n:ℝ) := signed_triangular_choose_sum n hn
  have hL : signedLogForm n = -2*(∑ j ∈ range (n+1), ∑ i ∈ range j,
      c i j/(j-i:ℕ)*B i j) := rfl
  have hoff : 2*(∑ j ∈ range (n+1), ∑ i ∈ range j,
      c i j/(j-i:ℕ)*(∑ k ∈ range (j-i), Real.log ((n+i+N+k+1:ℕ)/(n+i+k+1:ℝ)))) =
      -((2*n).choose n:ℝ)*Real.log N + signedLogForm n +
        2*(∑ j ∈ range (n+1), ∑ i ∈ range j, c i j/(j-i:ℕ)*E i j) := by
    calc
      _ = 2*(∑ j ∈ range (n+1), ∑ i ∈ range j,
          (c i j*Real.log N-c i j/(j-i:ℕ)*B i j+c i j/(j-i:ℕ)*E i j)) := by
        congr 1
        apply sum_congr rfl
        intro j hj
        apply sum_congr rfl
        intro i hi
        have hij : i < j := mem_range.mp hi
        simpa only [B, E, Nat.cast_add] using
          weighted_boundary_log_split (n+i) N (j-i) hN (by omega) (c i j)
      _ = _ := by
        simp_rw [sum_add_distrib, sum_sub_distrib, ← sum_mul]
        rw [hL]
        nlinarith [congrArg (fun z : ℝ => z*Real.log N) hcoeff]
  rw [finite_cutoff_evaluation n N hn, diagonal_cutoff_split]
  change _ + 2*(∑ j ∈ range (n+1), ∑ i ∈ range j,
    c i j/(j-i:ℕ)*(∑ k ∈ range (j-i), Real.log ((n+i+N+k+1:ℕ)/(n+i+k+1:ℝ)))) = _
  rw [hoff]
  unfold cutoffError
  rw [← correction_triangle_eq]
  dsimp only [c, E]
  ring

/-- Exact original finite-cutoff statement, conditional only on the logarithmic-form identity. -/
theorem finite_cutoff_identity_of_logarithmic_forms_equal (n N : ℕ)
    (hn : 0 < n) (hN : 0 < N) (hL : signedLogForm n = L n) :
    I n - remainder n N = ((2*n).choose n:ℝ) *
      ((harmonic N:ℝ)-Real.log N) + L n - (A n:ℝ) + cutoffError n N := by
  simpa only [hL] using finite_cutoff_signed_identity n N hn hN

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowAlternatingReciprocals
section
open Finset

namespace EulerMascheroni.Sondow

theorem alternating_choose_div_succ (n : ℕ) :
    (∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)/(j+1:ℕ)) = 1/(n+1:ℕ) := by
  have halt := signed_choose_sum (n+1) (by omega)
  rw [sum_range_succ'] at halt
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at halt
  have he (j : ℕ) : (-1:ℝ)^j*(n.choose j:ℝ)/(j+1:ℕ) =
      -((-1:ℝ)^(j+1)*((n+1).choose (j+1):ℝ))/(n+1:ℕ) := by
    have hc : (n+1:ℕ)*(n.choose j:ℝ) = ((n+1).choose (j+1):ℝ)*(j+1:ℕ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n j
    have hn0 : (n+1:ℕ) ≠ (0:ℝ) := by positivity
    have hj0 : (j+1:ℕ) ≠ (0:ℝ) := by positivity
    rw [pow_succ]
    field_simp
    nlinarith [congrArg (fun z : ℝ => (-1:ℝ)^j*z) hc]
  simp_rw [he, ← sum_div, sum_neg_distrib]
  congr 1
  linarith

/-- Pascal recurrence as a finite difference operator on a test sequence. -/
theorem alternating_choose_pascal (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ range (n+2), (-1:ℝ)^j*((n+1).choose j:ℝ)*f j) =
      (∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)*f j) -
        ∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)*f (j+1) := by
  have htail := sum_range_succ' (fun j => (-1:ℝ)^j*(n.choose j:ℝ)*f j) (n+1)
  rw [sum_range_succ] at htail
  simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero,
    pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at htail
  have he (j : ℕ) : (-1:ℝ)^(j+1)*((n+1).choose (j+1):ℝ)*f (j+1) =
      -((-1:ℝ)^j*(n.choose j:ℝ)*f (j+1)) +
        (-1:ℝ)^(j+1)*(n.choose (j+1):ℝ)*f (j+1) := by
    rw [Nat.choose_succ_succ', Nat.cast_add, pow_succ]
    ring
  rw [show n+2 = (n+1)+1 by omega, sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
  simp_rw [he, sum_add_distrib, sum_neg_distrib]
  linarith

theorem alternating_choose_div_index (n : ℕ) :
    (∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)/(j:ℝ)) = -(harmonic n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he := alternating_choose_pascal n (fun j => (j:ℝ)⁻¹)
    simp only [← div_eq_mul_inv] at he
    rw [he, ih, alternating_choose_div_succ, harmonic_succ]
    push_cast
    ring

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowBinomialRows
section
open Finset

namespace EulerMascheroni.Sondow

noncomputable def binomialRow (n k : ℕ) : ℝ :=
  ∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)/((j:ℝ)-k)

theorem binomialRow_zero (n : ℕ) : binomialRow n 0 = -(harmonic n:ℝ) := by
  simpa [binomialRow] using alternating_choose_div_index n

theorem binomialRow_pascal (n k : ℕ) :
    binomialRow (n+1) (k+1) = binomialRow n (k+1) - binomialRow n k := by
  have he := alternating_choose_pascal n (fun j => ((j:ℝ)-(k+1:ℕ))⁻¹)
  simpa [binomialRow, div_eq_mul_inv] using he

theorem neg_one_pow_complement (n j : ℕ) (hj : j ≤ n) :
    (-1:ℝ)^(n-j) = (-1:ℝ)^n*(-1:ℝ)^j := by
  have hsq : (-1:ℝ)^j*(-1:ℝ)^j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  conv_rhs => rw [← Nat.sub_add_cancel hj, pow_add]
  rw [mul_assoc, hsq, mul_one]

theorem binomialRow_self (n : ℕ) : binomialRow n n = (-1:ℝ)^n*(harmonic n:ℝ) := by
  unfold binomialRow
  rw [← sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  have he (j : ℕ) (hj : j ∈ range (n+1)) :
      (-1:ℝ)^(n-j)*(n.choose (n-j):ℝ)/((n-j:ℕ)-n:ℝ) =
        -(-1:ℝ)^n*((-1:ℝ)^j*(n.choose j:ℝ)/(j:ℝ)) := by
    have hjn : j ≤ n := by simpa using mem_range.mp hj
    rw [Nat.choose_symm hjn, Nat.cast_sub hjn, neg_one_pow_complement n j hjn]
    ring
  rw [sum_congr rfl he, ← mul_sum, alternating_choose_div_index]
  ring

theorem binomial_row_formula_pascal (n k : ℕ) (hk : k < n) :
    (-1:ℝ)^(k+1)*(n.choose (k+1):ℝ)*
        ((harmonic (k+1):ℝ)-(harmonic (n-(k+1)):ℝ)) -
      (-1:ℝ)^k*(n.choose k:ℝ)*((harmonic k:ℝ)-(harmonic (n-k):ℝ)) =
    (-1:ℝ)^(k+1)*((n+1).choose (k+1):ℝ)*
      ((harmonic (k+1):ℝ)-(harmonic ((n+1)-(k+1)):ℝ)) := by
  have hc : (n.choose (k+1):ℝ)/(n-k:ℕ) = (n.choose k:ℝ)/(k+1:ℕ) := by
    have hnk : (n-k:ℕ) ≠ (0:ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hk).ne'
    apply (div_eq_div_iff hnk (by positivity)).mpr
    exact_mod_cast Nat.choose_succ_right_eq n k
  have hH : (harmonic (n-k):ℝ) = (harmonic (n-(k+1)):ℝ) + 1/(n-k:ℕ) := by
    have hi : n-k = n-(k+1)+1 := by omega
    conv_lhs => rw [hi, harmonic_succ]
    push_cast
    rw [hi]
    push_cast
    ring
  have hK : (harmonic (k+1):ℝ) = (harmonic k:ℝ)+1/(k+1:ℕ) := by
    rw [harmonic_succ]
    push_cast
    ring
  rw [Nat.choose_succ_succ', Nat.cast_add, Nat.add_sub_add_right, hH, hK, pow_succ]
  linear_combination -(-1:ℝ)^k * hc

/-- Finite row identity underlying Sondow's Appendix combinatorial formula. -/
theorem binomialRow_eq_harmonic (n k : ℕ) (hk : k ≤ n) :
    binomialRow n k = (-1:ℝ)^k*(n.choose k:ℝ)*
      ((harmonic k:ℝ)-(harmonic (n-k):ℝ)) := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp [binomialRow_zero]
  | succ n ih =>
    by_cases hk0 : k = 0
    · subst k
      simp [binomialRow_zero]
    by_cases hkn : k = n+1
    · subst k
      simp [binomialRow_self]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hki : k+1 ≤ n := by omega
    rw [binomialRow_pascal, ih (k+1) hki, ih k (by omega)]
    exact binomial_row_formula_pascal n k (by omega)

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowRectangleIdentity
section
open Finset

namespace EulerMascheroni.Sondow

theorem skew_square_sum_zero (f : ℕ → ℕ → ℝ) (hf : ∀ i j, f i j = -f j i) (k : ℕ) :
    (∑ i ∈ range k, ∑ j ∈ range k, f i j) = 0 := by
  have he : (∑ i ∈ range k, ∑ j ∈ range k, f i j) =
      -(∑ i ∈ range k, ∑ j ∈ range k, f i j) := by
    calc
      _ = ∑ j ∈ range k, ∑ i ∈ range k, f i j := sum_comm
      _ = ∑ j ∈ range k, ∑ i ∈ range k, -f j i := by
        apply sum_congr rfl
        intro j hj
        apply sum_congr rfl
        intro i hi
        exact hf i j
      _ = _ := by simp only [sum_neg_distrib]
  linarith

noncomputable def binomialInteraction (n i j : ℕ) : ℝ :=
  -((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/((j:ℝ)-i)

theorem binomialInteraction_skew (n i j : ℕ) :
    binomialInteraction n i j = -binomialInteraction n j i := by
  unfold binomialInteraction
  rw [Nat.add_comm j i, show (i:ℝ)-j = -((j:ℝ)-i) by ring]
  rw [div_neg]
  ring

theorem binomialInteraction_row (n i : ℕ) (hi : i ≤ n) :
    (∑ j ∈ range (n+1), binomialInteraction n i j) =
      (n.choose i:ℝ)^2*((harmonic (n-i):ℝ)-(harmonic i:ℝ)) := by
  have he : (∑ j ∈ range (n+1), binomialInteraction n i j) =
      -((-1:ℝ)^i*(n.choose i:ℝ))*binomialRow n i := by
    rw [binomialRow, mul_sum]
    apply sum_congr rfl
    intro j hj
    unfold binomialInteraction
    rw [pow_add]
    ring
  rw [he, binomialRow_eq_harmonic n i hi]
  have hsq : (-1:ℝ)^i*(-1:ℝ)^i = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  linear_combination -(n.choose i:ℝ)^2*((harmonic i:ℝ)-(harmonic (n-i):ℝ))*hsq

/-- Sondow's Appendix rectangle identity, expressed without a negative natural exponent. -/
theorem binomial_rectangle_identity (n k : ℕ) (hk : k ≤ n+1) :
    (∑ i ∈ range k, ∑ j ∈ Ico k (n+1),
      -((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ)) =
      ∑ i ∈ range k, (n.choose i:ℝ)^2*
        ((harmonic (n-i):ℝ)-(harmonic i:ℝ)) := by
  have he : (∑ i ∈ range k, ∑ j ∈ Ico k (n+1),
      -((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ)) =
      ∑ i ∈ range k, ∑ j ∈ Ico k (n+1), binomialInteraction n i j := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    have hij : i ≤ j := by
      have := mem_range.mp hi
      have := (mem_Ico.mp hj).1
      omega
    simp only [binomialInteraction, Nat.cast_sub hij]
  rw [he]
  simp_rw [sum_Ico_eq_sub _ hk, sum_sub_distrib]
  rw [skew_square_sum_zero _ (binomialInteraction_skew n) k, sub_zero]
  apply sum_congr rfl
  intro i hi
  exact binomialInteraction_row n i (by have := mem_range.mp hi; omega)

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowPrefixSymmetry
section
open Finset

namespace EulerMascheroni.Sondow

theorem antisymmetric_prefix_reflection (w : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n+1)
    (hw : ∀ i ≤ n, w (n-i) = -w i) :
    (∑ i ∈ range k, w i) = ∑ i ∈ range (n+1-k), w i := by
  have hfull : (∑ i ∈ range (n+1), w i) = 0 := by
    have he : (∑ i ∈ range (n+1), w i) = -(∑ i ∈ range (n+1), w i) := by
      conv_lhs => rw [← sum_range_reflect]
      simp only [Nat.add_sub_cancel]
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i hi
      exact hw i (by have := mem_range.mp hi; omega)
    linarith
  have htail : (∑ j ∈ range (n+1-k), w (k+j)) = -(∑ i ∈ range (n+1-k), w i) := by
    conv_lhs => rw [← sum_range_reflect]
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i hi
    have hi' : i < n+1-k := mem_range.mp hi
    rw [show k+(n+1-k-1-i) = n-i by omega]
    exact hw i (by omega)
  have hsplit := sum_range_add w k (n+1-k)
  rw [Nat.add_sub_of_le hk, hfull, htail] at hsplit
  linarith

noncomputable def harmonicRowWeight (n i : ℕ) : ℝ :=
  (n.choose i:ℝ)^2*((harmonic (n-i):ℝ)-(harmonic i:ℝ))

theorem harmonicRowWeight_reflection (n i : ℕ) (hi : i ≤ n) :
    harmonicRowWeight n (n-i) = -harmonicRowWeight n i := by
  unfold harmonicRowWeight
  rw [Nat.choose_symm hi, Nat.sub_sub_self hi]
  ring

theorem harmonic_prefix_min (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (∑ i ∈ range k, harmonicRowWeight n i) =
      ∑ i ∈ range (min (k-1) (n-k)+1), harmonicRowWeight n i := by
  by_cases hh : k-1 ≤ n-k
  · rw [min_eq_left hh, Nat.sub_add_cancel hk]
  · rw [min_eq_right (by omega)]
    have he := antisymmetric_prefix_reflection (harmonicRowWeight n) n k (by omega)
      (harmonicRowWeight_reflection n)
    simpa only [show n+1-k = n-k+1 by omega] using he

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowTripleReindex
section
open Finset

namespace EulerMascheroni.Sondow

theorem triangle_interval_sum_reindex (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range (n+1), ∑ i ∈ range j, ∑ k ∈ Icc (i+1) j, f i j k) =
      ∑ k ∈ Icc 1 n, ∑ i ∈ range k, ∑ j ∈ Ico k (n+1), f i j k := by
  have hleft (j : ℕ) : (∑ i ∈ range j, ∑ k ∈ Icc (i+1) j, f i j k) =
      ∑ p ∈ (range j).sigma (fun i => Icc (i+1) j), f p.1 j p.2 := sum_sigma' ..
  have hright (k : ℕ) : (∑ i ∈ range k, ∑ j ∈ Ico k (n+1), f i j k) =
      ∑ p ∈ (range k).sigma (fun _ => Ico k (n+1)), f p.1 p.2 k := sum_sigma' ..
  simp_rw [hleft, hright]
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2.2, ⟨x.2.1, x.1⟩⟩)
    (fun x => ⟨x.2.2, ⟨x.2.1, x.1⟩⟩) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) <;>
    simp only [mem_sigma, mem_range, mem_Icc, mem_Ico, Sigma.forall] <;> omega

end EulerMascheroni.Sondow
end

-- Source: Solutions.SondowLogarithmicForms
section
open Finset

namespace EulerMascheroni.Sondow

theorem harmonic_interval_sum (a b : ℕ) (hab : a ≤ b) :
    (∑ j ∈ Icc (a+1) b, (1:ℝ)/j) = (harmonic b:ℝ)-(harmonic a:ℝ) := by
  have hI : Icc (a+1) b = Ico (a+1) (b+1) := by
    ext j
    simp only [mem_Icc, mem_Ico]
    omega
  have hs (m : ℕ) : (∑ j ∈ range (m+1), (1:ℝ)/j) = (harmonic m:ℝ) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero]
    simp only [harmonic]
    push_cast
    simp only [one_div]
  rw [hI, sum_Ico_eq_sub _ (by omega), hs, hs]

theorem shifted_log_interval (n i j : ℕ) :
    (∑ r ∈ range (j-i), Real.log (n+i+r+1:ℕ)) =
      ∑ k ∈ Icc (i+1) j, Real.log (n+k:ℕ) := by
  have hI : Icc (i+1) j = Ico (i+1) (j+1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hI, sum_Ico_eq_sum_range, Nat.add_sub_add_right]
  apply sum_congr rfl
  intro r hr
  congr 2
  omega

theorem L_eq_harmonic_prefix (n : ℕ) :
    L n = 2*(∑ k ∈ Icc 1 n, (∑ i ∈ range k, harmonicRowWeight n i)*Real.log (n+k:ℕ)) := by
  unfold L
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk0 : 0 < k := (mem_Icc.mp hk).1
  have hkn : k ≤ n := (mem_Icc.mp hk).2
  rw [harmonic_prefix_min n k hk0 hkn]
  have hI : Icc 0 (min (k-1) (n-k)) = range (min (k-1) (n-k)+1) := by
    ext i
    simp only [mem_Icc, mem_range]
    omega
  rw [hI, sum_mul, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ min (k-1) (n-k) := by have := mem_range.mp hi; omega
  have hineq : i ≤ n-i := by have := (le_min_iff.mp hi'); omega
  calc
    _ = 2*(n.choose i:ℝ)^2*(∑ j ∈ Icc (i+1) (n-i), (1:ℝ)/j)*Real.log (n+k:ℕ) := by
      rw [mul_sum, sum_mul]
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [harmonic_interval_sum i (n-i) hineq]; unfold harmonicRowWeight; ring

theorem signedLogForm_eq_harmonic_prefix (n : ℕ) :
    signedLogForm n =
      2*(∑ k ∈ Icc 1 n, (∑ i ∈ range k, harmonicRowWeight n i)*Real.log (n+k:ℕ)) := by
  let c (i j : ℕ) : ℝ := (-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)
  have ht (i j : ℕ) : -(c i j/(j-i:ℕ)*(∑ r ∈ range (j-i), Real.log (n+i+r+1:ℕ))) =
      ∑ k ∈ Icc (i+1) j, -c i j/(j-i:ℕ)*Real.log (n+k:ℕ) := by
    rw [shifted_log_interval, mul_sum, ← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    ring
  calc
    _ = 2*(∑ j ∈ range (n+1), ∑ i ∈ range j,
        -(c i j/(j-i:ℕ)*(∑ r ∈ range (j-i), Real.log (n+i+r+1:ℕ)))) := by
      simp only [sum_neg_distrib, signedLogForm, c]
      ring
    _ = 2*(∑ k ∈ Icc 1 n, ∑ i ∈ range k, ∑ j ∈ Ico k (n+1),
        -c i j/(j-i:ℕ)*Real.log (n+k:ℕ)) := by
      simp_rw [ht]
      rw [triangle_interval_sum_reindex]
    _ = _ := by
      simp_rw [← sum_mul]
      congr 1
      apply sum_congr rfl
      intro k hk
      rw [show (∑ i ∈ range k, ∑ j ∈ Ico k (n+1), -c i j/(j-i:ℕ)) =
          ∑ i ∈ range k, harmonicRowWeight n i from
        binomial_rectangle_identity n k (by have := (mem_Icc.mp hk).2; omega)]

theorem signedLogForm_eq_L (n : ℕ) : signedLogForm n = L n := by
  rw [signedLogForm_eq_harmonic_prefix, L_eq_harmonic_prefix]

end EulerMascheroni.Sondow
end

open EulerMascheroni.Sondow

theorem solution (n N : ℕ) (hn : 0 < n) (hN : 0 < N) :
    I n - remainder n N = ((2*n).choose n : ℝ) *
      ((harmonic N : ℝ)-Real.log N) + L n - (A n : ℝ) + cutoffError n N := by
  exact finite_cutoff_identity_of_logarithmic_forms_equal n N hn hN (signedLogForm_eq_L n)

#print axioms solution
