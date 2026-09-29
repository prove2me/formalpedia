-- Prove2me | solution 1 for Complex.integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/caeb969c-3c17-54fa-9d94-dd5241e571c0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg

set_option autoImplicit false

p2m_open "MeasureTheory Set Real Complex P2MW.S_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg.Complex"

noncomputable section

namespace Complex
p2m_export "Complex" "one_re measurable_ofReal one_cpow re norm_cpow_eq_rpow_re_of_pos ofReal_re add_re ofReal_ne_zero norm_real real_smul cpow_ne_zero_iff cpow_one Gamma cpow_neg ofReal_mul neg_re sub_re inv_cpow cpow_add integral_cpow_mul_exp_neg_mul_Ioi Gamma_ne_zero_of_re_pos mul_cpow_ofReal_nonneg exp arg_ofReal_of_nonneg norm_exp ofReal_one mul_re ofReal_im exp_add"
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

namespace Complex p2m_export "Complex" "one_re measurable_ofReal one_cpow re norm_cpow_eq_rpow_re_of_pos ofReal_re add_re ofReal_ne_zero norm_real real_smul cpow_ne_zero_iff cpow_one Gamma cpow_neg ofReal_mul neg_re sub_re inv_cpow cpow_add integral_cpow_mul_exp_neg_mul_Ioi Gamma_ne_zero_of_re_pos mul_cpow_ofReal_nonneg exp arg_ofReal_of_nonneg norm_exp ofReal_one mul_re ofReal_im exp_add" namespace BetaHalfLine end Complex.BetaHalfLine
p2m_open_scoped "Complex" in
open Complex.BetaHalfLine in
theorem Complex.BetaHalfLine.betaHalfLine
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

namespace Complex
p2m_export "Complex" "one_re measurable_ofReal one_cpow re norm_cpow_eq_rpow_re_of_pos ofReal_re add_re ofReal_ne_zero norm_real real_smul cpow_ne_zero_iff cpow_one Gamma cpow_neg ofReal_mul neg_re sub_re inv_cpow cpow_add integral_cpow_mul_exp_neg_mul_Ioi Gamma_ne_zero_of_re_pos mul_cpow_ofReal_nonneg exp arg_ofReal_of_nonneg norm_exp ofReal_one mul_re ofReal_im exp_add"
namespace Dirichlet2
p2m_open "Complex"

open Complex.BetaHalfLine

noncomputable def f (α β γ : ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) * (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ)

noncomputable def g (α β γ : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((p.2 : ℂ) ^ (β - 1) * (((1 + p.2 : ℝ)) : ℂ) ^ (-γ)) *
    ((p.1 : ℂ) ^ (α + β - γ - 1) * Complex.exp (-((((1 + p.2 : ℝ)) : ℂ) * (p.1 : ℂ))))

theorem measurable_f (α β γ : ℂ) : Measurable (f α β γ) := by
  unfold f
  have hs : Measurable (fun p : ℝ × ℝ => (((p.1 + p.2 : ℝ)) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_fst.add measurable_snd)
  exact (((Measurable.cexp hs.neg).mul ((Complex.measurable_ofReal.comp measurable_fst).pow_const _)).mul
    ((Complex.measurable_ofReal.comp measurable_snd).pow_const _)).mul (hs.pow_const _)

theorem measurable_g (α β γ : ℂ) : Measurable (g α β γ) := by
  unfold g
  have h1 : Measurable (fun p : ℝ × ℝ => (((1 + p.2 : ℝ)) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_const.add measurable_snd)
  exact (((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul (h1.pow_const _)).mul
    (((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul
      (Measurable.cexp (h1.mul (Complex.measurable_ofReal.comp measurable_fst)).neg))

theorem tau_mul_f_eq_g (α β γ : ℂ) {τ v : ℝ} (hτ : 0 < τ) (hv : 0 < v) :
    (τ : ℂ) * f α β γ (τ, τ * v) = g α β γ (τ, v) := by
  have hτ0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
  simp only [f, g]
  have e1 : (((τ + τ * v : ℝ)) : ℂ) = ((τ : ℝ) : ℂ) * (((1 + v : ℝ)) : ℂ) := by push_cast; ring
  have e2 : (((τ * v : ℝ)) : ℂ) ^ (β - 1) = (τ : ℂ) ^ (β - 1) * (v : ℂ) ^ (β - 1) := by
    rw [Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg hτ.le hv.le _
  have e3 : (((τ : ℝ) : ℂ) * (((1 + v : ℝ)) : ℂ)) ^ (-γ) = (τ : ℂ) ^ (-γ) * (((1 + v : ℝ)) : ℂ) ^ (-γ) :=
    Complex.mul_cpow_ofReal_nonneg hτ.le (by positivity) _
  have e4 : Complex.exp (-(((τ : ℝ) : ℂ) * (((1 + v : ℝ)) : ℂ))) = Complex.exp (-((((1 + v : ℝ)) : ℂ) * (τ : ℂ))) := by
    ring_nf
  rw [e1, e2, e3, e4]
  have e5 : (τ : ℂ) * (τ : ℂ) ^ (α - 1) * (τ : ℂ) ^ (β - 1) * (τ : ℂ) ^ (-γ) = (τ : ℂ) ^ (α + β - γ - 1) := by
    rw [show (τ : ℂ) * (τ : ℂ) ^ (α - 1) = (τ : ℂ) ^ (1 : ℂ) * (τ : ℂ) ^ (α - 1) by rw [Complex.cpow_one],
      ← Complex.cpow_add _ _ hτ0, ← Complex.cpow_add _ _ hτ0, ← Complex.cpow_add _ _ hτ0]
    congr 1; ring
  calc (τ : ℂ) * (Complex.exp (-((((1 + v : ℝ)) : ℂ) * (τ : ℂ))) * (τ : ℂ) ^ (α - 1) *
        ((τ : ℂ) ^ (β - 1) * (v : ℂ) ^ (β - 1)) * ((τ : ℂ) ^ (-γ) * (((1 + v : ℝ)) : ℂ) ^ (-γ)))
      = ((v : ℂ) ^ (β - 1) * (((1 + v : ℝ)) : ℂ) ^ (-γ)) *
        (((τ : ℂ) * (τ : ℂ) ^ (α - 1) * (τ : ℂ) ^ (β - 1) * (τ : ℂ) ^ (-γ)) *
          Complex.exp (-((((1 + v : ℝ)) : ℂ) * (τ : ℂ)))) := by ring
    _ = _ := by rw [e5]

theorem norm_g (α β γ : ℂ) {τ v : ℝ} (hτ : 0 < τ) (hv : 0 < v) :
    ‖g α β γ (τ, v)‖ = (v ^ (β.re - 1) * (1 + v) ^ (-γ.re)) *
      (τ ^ ((α + β - γ).re - 1) * Real.exp (-((1 + v) * τ))) := by
  simp only [g, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_cpow_eq_rpow_re_of_pos hτ,
    Complex.norm_cpow_eq_rpow_re_of_pos (show (0:ℝ) < 1 + v by positivity), Complex.norm_exp,
    Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

theorem integrable_g (α β γ : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < (α + β - γ).re) :
    Integrable (g α β γ) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [integrable_prod_iff' (measurable_g α β γ).aestronglyMeasurable]
  constructor
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun v hv => ?_)
    have hv : 0 < v := hv
    have h1 := (integrableOn_rpow_mul_exp_neg_mul hγ (show (0:ℝ) < 1 + v by positivity)).const_mul
      (v ^ (β.re - 1) * (1 + v) ^ (-γ.re))
    refine h1.mono' ((measurable_g α β γ).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun τ hτ => ?_)
    rw [norm_g α β γ hτ hv]
  ·
    have hB := (betaHalfLine (β.re : ℂ) (α.re : ℂ) (by simpa) (by simpa)).1
    have hBn := (hB.norm).const_mul (Real.Gamma ((α + β - γ).re))
    refine IntegrableOn.congr_fun hBn (fun v hv => ?_) measurableSet_Ioi
    have hv : 0 < v := hv
    have h1v : (0 : ℝ) < 1 + v := by positivity
    rw [setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => norm_g α β γ hτ hv), integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hγ h1v, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv,
      Complex.norm_cpow_eq_rpow_re_of_pos h1v]
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.neg_re, Complex.add_re]
    rw [one_div, Real.inv_rpow h1v.le, ← Real.rpow_neg h1v.le]
    have e : (1 + v) ^ (-γ.re) * (1 + v) ^ (-(α.re + β.re - γ.re)) = (1 + v) ^ (-(β.re + α.re)) := by
      rw [← Real.rpow_add h1v]; congr 1; ring
    rw [← e]; ring

theorem integrable_f (α β γ : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < (α + β - γ).re) :
    Integrable (f α β γ) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hg := integrable_g α β γ hα hβ hγ
  rw [integrable_prod_iff (measurable_g α β γ).aestronglyMeasurable] at hg
  obtain ⟨hg1, hg2⟩ := hg
  rw [integrable_prod_iff (measurable_f α β γ).aestronglyMeasurable]
  constructor
  ·
    filter_upwards [hg1, ae_restrict_mem measurableSet_Ioi] with τ hτg hτ
    have hτ : 0 < τ := hτ
    have hτ0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'

    have h1 : IntegrableOn (fun v : ℝ => f α β γ (τ, τ * v)) (Ioi 0) := by
      have h2 := hτg.const_mul ((τ : ℂ)⁻¹)
      refine IntegrableOn.congr_fun h2 (fun v hv => ?_) measurableSet_Ioi
      rw [← tau_mul_f_eq_g α β γ hτ hv, ← mul_assoc, inv_mul_cancel₀ hτ0, one_mul]
    have h3 := (integrableOn_Ioi_comp_mul_left_iff (fun σ : ℝ => f α β γ (τ, σ)) 0 hτ).mp h1
    rwa [mul_zero] at h3
  ·
    refine hg2.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    have hτ : 0 < τ := hτ
    have hsub := integral_comp_mul_left_Ioi (fun σ : ℝ => ‖f α β γ (τ, σ)‖) 0 hτ
    rw [mul_zero] at hsub

    have e : ∫ v in Ioi (0 : ℝ), ‖g α β γ (τ, v)‖ = τ * ∫ v in Ioi (0 : ℝ), ‖f α β γ (τ, τ * v)‖ := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
      rw [← tau_mul_f_eq_g α β γ hτ hv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
    rw [e, hsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul]

theorem integral_f (α β γ : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < (α + β - γ).re) :
    ∫ p : ℝ × ℝ, f α β γ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      Complex.Gamma (α + β - γ) * Complex.Gamma α * Complex.Gamma β / Complex.Gamma (α + β) := by
  have hf := integrable_f α β γ hα hβ hγ
  have hg := integrable_g α β γ hα hβ hγ
  rw [integral_prod _ hf]

  have h1 : ∫ τ in Ioi (0 : ℝ), ∫ σ in Ioi (0 : ℝ), f α β γ (τ, σ) =
      ∫ τ in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), g α β γ (τ, v) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => ?_)
    have hτ : 0 < τ := hτ
    have hsub := integral_comp_mul_left_Ioi (fun σ : ℝ => f α β γ (τ, σ)) 0 hτ
    rw [mul_zero] at hsub
    have e : ∫ v in Ioi (0 : ℝ), g α β γ (τ, v) = (τ : ℂ) * ∫ v in Ioi (0 : ℝ), f α β γ (τ, τ * v) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun v hv => (tau_mul_f_eq_g α β γ hτ hv).symm)
    rw [e, hsub, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hτ.ne',
      Complex.ofReal_one, one_mul]
  rw [h1, integral_integral_swap (f := fun τ v => g α β γ (τ, v)) hg]

  have h2 : ∫ v in Ioi (0 : ℝ), ∫ τ in Ioi (0 : ℝ), g α β γ (τ, v) =
      ∫ v in Ioi (0 : ℝ), Complex.Gamma (α + β - γ) *
        ((v : ℂ) ^ (β - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(β + α))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    have hv : 0 < v := hv
    have h1v : (0 : ℝ) < 1 + v := by positivity
    have h1v0 : (((1 + v : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1v.ne'
    rw [show (fun τ : ℝ => g α β γ (τ, v)) = fun τ : ℝ => ((v : ℂ) ^ (β - 1) * (((1 + v : ℝ)) : ℂ) ^ (-γ)) *
        ((τ : ℂ) ^ (α + β - γ - 1) * Complex.exp (-((((1 + v : ℝ)) : ℂ) * (τ : ℂ)))) from rfl,
      integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hγ h1v, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg h1v.le]; exact Real.pi_ne_zero.symm),
      ← Complex.cpow_neg]
    have e : (((1 + v : ℝ)) : ℂ) ^ (-γ) * (((1 + v : ℝ)) : ℂ) ^ (-(α + β - γ)) = (((1 + v : ℝ)) : ℂ) ^ (-(β + α)) := by
      rw [← Complex.cpow_add _ _ h1v0]; congr 1; ring
    calc (v : ℂ) ^ (β - 1) * (((1 + v : ℝ)) : ℂ) ^ (-γ) * ((((1 + v : ℝ)) : ℂ) ^ (-(α + β - γ)) * Complex.Gamma (α + β - γ))
        = Complex.Gamma (α + β - γ) * ((v : ℂ) ^ (β - 1) * ((((1 + v : ℝ)) : ℂ) ^ (-γ) * (((1 + v : ℝ)) : ℂ) ^ (-(α + β - γ)))) := by
          ring
      _ = _ := by rw [e]
  rw [h2, integral_const_mul, (betaHalfLine β α hβ hα).2, show β + α = α + β by ring]
  field_simp

end Complex.Dirichlet2

open Complex.Dirichlet2 in
theorem solution
    (α β γ : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < (α + β - γ).re) :
    Integrable (fun p : ℝ × ℝ => Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) *
        (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
      ∫ p : ℝ × ℝ, Complex.exp (-(((p.1 + p.2 : ℝ)) : ℂ)) * (p.1 : ℂ) ^ (α - 1) *
          (p.2 : ℂ) ^ (β - 1) * (((p.1 + p.2 : ℝ)) : ℂ) ^ (-γ)
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) =
        Complex.Gamma (α + β - γ) * Complex.Gamma α * Complex.Gamma β / Complex.Gamma (α + β) := by
  exact ⟨integrable_f α β γ hα hβ hγ, integral_f α β γ hα hβ hγ⟩

#print axioms solution

end S_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg
end P2MW
export P2MW.S_Complex_integrable_and_integral_prod_Ioi_exp_neg_add_mul_cpow_mul_cpow_mul_add_cpow_neg (solution)
