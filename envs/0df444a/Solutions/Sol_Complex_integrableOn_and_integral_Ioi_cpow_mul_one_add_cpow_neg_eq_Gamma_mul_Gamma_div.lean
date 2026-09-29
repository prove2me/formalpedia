-- Prove2me | solution 1 for Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1b46adf9-69a2-569c-9ad3-3eb9987aa924

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div

set_option autoImplicit false

p2m_open "MeasureTheory Set Real Complex P2MW.S_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div.Complex"

noncomputable section

namespace Complex
p2m_export "Complex" "one_re measurable_ofReal one_cpow re norm_cpow_eq_rpow_re_of_pos ofReal_re ofReal_ne_zero cpow_ne_zero_iff Gamma cpow_neg neg_re sub_re inv_cpow cpow_add integral_cpow_mul_exp_neg_mul_Ioi Gamma_ne_zero_of_re_pos exp arg_ofReal_of_nonneg norm_exp mul_re ofReal_im exp_add"
namespace BetaHalfLine
p2m_open "Complex"

theorem integrable_of_integral_ne_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E} (h : ∫ x, f x ∂μ ≠ 0) : Integrable f μ := by
  by_contra hf
  exact h (integral_undef hf)

theorem integrableOn_cpow_mul_exp_neg_mul {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * Complex.exp (-((r : ℂ) * (t : ℂ)))) (Ioi 0) := by
  apply integrable_of_integral_ne_zero
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hr]
  exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by
    rw [one_div]; exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')))) (Complex.Gamma_ne_zero_of_re_pos ha)

theorem integrableOn_rpow_mul_exp_neg_mul {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  apply integrable_of_integral_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  exact mul_ne_zero (by positivity) (Real.Gamma_pos_of_pos ha).ne'

def B (a b : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (a - 1) * ((p.2 : ℂ) ^ (a + b - 1) * Complex.exp (-((((1 + p.1 : ℝ)) : ℂ) * (p.2 : ℂ))))

theorem measurable_B (a b : ℂ) : Measurable (B a b) := by
  unfold B
  refine ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul
    (((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul (Measurable.cexp ?_))
  exact ((Complex.measurable_ofReal.comp (measurable_const.add measurable_fst)).mul
    (Complex.measurable_ofReal.comp measurable_snd)).neg

theorem B_eq (a b : ℂ) (v y : ℝ) :
    B a b (v, y) = ((y : ℂ) ^ (a + b - 1) * Complex.exp (-(y : ℂ))) *
      ((v : ℂ) ^ (a - 1) * Complex.exp (-((y : ℂ) * (v : ℂ)))) := by
  simp only [B]
  have e : Complex.exp (-((((1 + v : ℝ)) : ℂ) * (y : ℂ))) =
      Complex.exp (-(y : ℂ)) * Complex.exp (-((y : ℂ) * (v : ℂ))) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [e]; ring

theorem norm_B (a b : ℂ) {v y : ℝ} (hv : 0 < v) (hy : 0 < y) :
    ‖B a b (v, y)‖ = (y ^ ((a + b).re - 1) * Real.exp (-y)) * (v ^ (a.re - 1) * Real.exp (-(y * v))) := by
  rw [B_eq, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv,
    Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.one_re, mul_zero, sub_zero]

theorem integrable_B (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    Integrable (B a b) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hab : 0 < (a + b).re := by simp; linarith
  rw [integrable_prod_iff' (measurable_B a b).aestronglyMeasurable]
  constructor
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun y hy => ?_)
    have hy : 0 < y := hy
    have h1 := (integrableOn_rpow_mul_exp_neg_mul ha hy).const_mul (y ^ ((a + b).re - 1) * Real.exp (-y))
    refine h1.mono' ((measurable_B a b).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun v hv => ?_)
    rw [norm_B a b hv hy]
  · have hI := (integrableOn_rpow_mul_exp_neg_mul hb one_pos).const_mul (Real.Gamma a.re)
    refine IntegrableOn.congr_fun hI (fun y hy => ?_) measurableSet_Ioi
    have hy : 0 < y := hy
    rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => norm_B a b hv hy), integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi ha hy, one_div y, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le]
    have e : y ^ ((a + b).re - 1) * y ^ (-a.re) = y ^ (b.re - 1) := by
      rw [← Real.rpow_add hy]; congr 1; simp; ring
    rw [show -((1 : ℝ) * y) = -y by ring, ← e]
    ring

theorem integral_B_snd (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) {v : ℝ} (hv : 0 < v) :
    ∫ y in Ioi (0 : ℝ), B a b (v, y) =
      (v : ℂ) ^ (a - 1) * ((1 / (((1 + v : ℝ)) : ℂ)) ^ (a + b) * Complex.Gamma (a + b)) := by
  have hab : 0 < (a + b).re := by simp; linarith
  rw [show (fun y : ℝ => B a b (v, y)) = fun y : ℝ => (v : ℂ) ^ (a - 1) *
      ((y : ℂ) ^ (a + b - 1) * Complex.exp (-((((1 + v : ℝ)) : ℂ) * (y : ℂ)))) from rfl,
    integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hab (by positivity)]

theorem integral_B_fst (a b : ℂ) (ha : 0 < a.re) {y : ℝ} (hy : 0 < y) :
    ∫ v in Ioi (0 : ℝ), B a b (v, y) =
      ((y : ℂ) ^ (a + b - 1) * Complex.exp (-(y : ℂ))) * ((1 / (y : ℂ)) ^ a * Complex.Gamma a) := by
  rw [show (fun v : ℝ => B a b (v, y)) = fun v : ℝ => ((y : ℂ) ^ (a + b - 1) * Complex.exp (-(y : ℂ))) *
      ((v : ℂ) ^ (a - 1) * Complex.exp (-((y : ℂ) * (v : ℂ)))) from funext fun v => B_eq a b v y,
    integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hy]

end Complex.BetaHalfLine

end

open Complex.BetaHalfLine in
theorem solution
    (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b))) (Set.Ioi 0) ∧
      ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b)) =
        Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by
  have hab : 0 < (a + b).re := by simp; linarith
  have hΓab : Complex.Gamma (a + b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hab
  have hB := integrable_B a b ha hb

  have hsec : ∀ v : ℝ, 0 < v → ∫ y in Ioi (0 : ℝ), B a b (v, y) =
      Complex.Gamma (a + b) * ((v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b))) := by
    intro v hv
    rw [integral_B_snd a b ha hb hv, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm),
      ← Complex.cpow_neg]
    ring

  have hswap : ∫ v in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), B a b (v, y) = ∫ y in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), B a b (v, y) :=
    integral_integral_swap (f := fun v y => B a b (v, y)) hB
  have hL : ∫ v in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), B a b (v, y) =
      Complex.Gamma (a + b) * ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => hsec v hv), integral_const_mul]
  have hR : ∫ y in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), B a b (v, y) = Complex.Gamma a * Complex.Gamma b := by
    have hpt : ∀ y : ℝ, 0 < y → ∫ v in Ioi (0 : ℝ), B a b (v, y) =
        Complex.Gamma a * ((y : ℂ) ^ (b - 1) * Complex.exp (-((((1 : ℝ)) : ℂ) * (y : ℂ)))) := by
      intro y hy
      have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      rw [integral_B_fst a b ha hy, one_div,
        Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm),
        ← Complex.cpow_neg]
      have e : (y : ℂ) ^ (a + b - 1) * (y : ℂ) ^ (-a) = (y : ℂ) ^ (b - 1) := by
        rw [← Complex.cpow_add _ _ hy0]; congr 1; ring
      push_cast; rw [one_mul]
      calc (y : ℂ) ^ (a + b - 1) * Complex.exp (-(y : ℂ)) * ((y : ℂ) ^ (-a) * Complex.Gamma a)
          = Complex.Gamma a * (((y : ℂ) ^ (a + b - 1) * (y : ℂ) ^ (-a)) * Complex.exp (-(y : ℂ))) := by ring
        _ = _ := by rw [e]
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => hpt y hy), integral_const_mul,
      Complex.integral_cpow_mul_exp_neg_mul_Ioi hb one_pos]
    push_cast; rw [div_one, Complex.one_cpow, one_mul]
  have hval : ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b)) =
      Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by
    rw [eq_div_iff hΓab, mul_comm, ← hL, hswap, hR]
  refine ⟨?_, hval⟩

  have h1 : Integrable (fun v : ℝ => ∫ y in Ioi (0 : ℝ), B a b (v, y)) (volume.restrict (Ioi 0)) :=
    hB.integral_prod_left
  have h2 := h1.const_mul (Complex.Gamma (a + b))⁻¹
  refine IntegrableOn.congr_fun h2 (fun v hv => ?_) measurableSet_Ioi
  rw [hsec v hv, ← mul_assoc, inv_mul_cancel₀ hΓab, one_mul]

#print axioms solution

end S_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div
end P2MW
export P2MW.S_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div (solution)
