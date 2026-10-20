-- Prove2me | solution 2 for CohnElkies.exists_stripPoissonKernel_uniform_abs_moment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:48:21.140253+00:00
-- url     : https://prove2.me/submissions/bfd1037c-a17a-43d9-b3a2-3e3fa7a52824

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
theorem h47_int_abs_pow_exp (n : ℕ) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := a)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos ha
  have hIoi : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi 0) := by
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := hx
    simp [abs_of_pos hx0, Real.rpow_natCast]
  have hIio : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iio 0) := by
    have := (show MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi (-0)) by
      simpa using hIoi).comp_neg_Iio
    simpa [abs_neg] using this
  have hall : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iic 0 ∪ Set.Ioi 0) :=
    ((integrableOn_Iic_iff_integrableOn_Iio (b := (0:ℝ))).mpr hIio).union hIoi
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at hall
  exact hall

theorem h47_strip_pw {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 1) (T : ℝ) :
    0 ≤ stripPoissonKernel σ T * |T| ∧
    stripPoissonKernel σ T * |T| ≤ 1 / 4 ∧
    (1 ≤ |T| → stripPoissonKernel σ T * |T| ≤ 2 * (|T| ^ 1 * Real.exp (-(Real.pi / 2) * |T|))) := by
  unfold stripPoissonKernel
  set θ := stripAngle σ with hθ
  have hθ0 : 0 < θ := by rw [hθ, stripAngle]; have := Real.pi_pos; nlinarith
  have hθπ : θ < Real.pi := by rw [hθ, stripAngle]; have := Real.pi_pos; nlinarith
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsc := Real.sin_sq_add_cos_sq θ
  have hc1 : Real.cos θ < 1 := by
    by_contra h; push Not at h; nlinarith [Real.cos_le_one θ]
  set y := Real.pi * |T| / 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hcosh : Real.cosh (Real.pi * T / 2) = (Real.exp y + Real.exp (-y)) / 2 := by
    rw [← Real.cosh_abs, Real.cosh_eq]; congr 3 <;> rw [hy, abs_div, abs_mul, abs_of_pos Real.pi_pos] <;> norm_num
  have hq := Real.quadratic_le_exp_of_nonneg hy0
  have hl := Real.add_one_le_exp (-y)
  have hen := Real.exp_pos (-y)
  have hA : 1 + y ^ 2 / 4 ≤ Real.cosh (Real.pi * T / 2) := by rw [hcosh]; nlinarith
  have hden : 0 < Real.cosh (Real.pi * T / 2) - Real.cos θ := by nlinarith [sq_nonneg y]
  have hT0 : 0 ≤ |T| := abs_nonneg T
  have hfac : 0 < 4 * (Real.cosh (Real.pi * T / 2) - Real.cos θ) := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ hfac]
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hy2 : y ^ 2 = Real.pi ^ 2 * |T| ^ 2 / 4 := by rw [hy]; ring
    have h8 : 8 < Real.pi ^ 2 := by nlinarith
    have hT2 : |T| ^ 2 / 2 ≤ y ^ 2 / 4 := by
      rw [hy2]; nlinarith [mul_le_mul_of_nonneg_right h8.le (sq_nonneg |T|)]
    nlinarith [sq_nonneg (Real.sin θ - |T|)]
  · intro hT1
    have hy1 : Real.pi / 2 ≤ y := by rw [hy]; nlinarith [Real.pi_pos]
    have hE : 3 ≤ Real.exp y := by
      have hpi : 3 < Real.pi := Real.pi_gt_three
      nlinarith
    have hcl : Real.exp y / 2 ≤ Real.cosh (Real.pi * T / 2) := by rw [hcosh]; linarith
    have hexp : Real.exp (-(Real.pi / 2) * |T|) = (Real.exp y)⁻¹ := by
      rw [← Real.exp_neg]; congr 1; rw [hy]; ring
    rw [hexp, pow_one, div_mul_eq_mul_div, div_le_iff₀ hfac]
    have hEp := Real.exp_pos y
    have hinv : (Real.exp y)⁻¹ * Real.exp y = 1 := inv_mul_cancel₀ hEp.ne'
    have hc : Real.cos θ ≤ 1 := hc1.le
    have key : Real.exp y / 2 ≤ 4 * (Real.cosh (Real.pi * T / 2) - Real.cos θ) := by linarith
    have hip : 0 < (Real.exp y)⁻¹ := inv_pos.mpr hEp
    calc Real.sin θ * |T| ≤ |T| := by nlinarith
      _ = 2 * (|T| * (Real.exp y)⁻¹) * (Real.exp y / 2) := by field_simp
      _ ≤ 2 * (|T| * (Real.exp y)⁻¹) * (4 * (Real.cosh (Real.pi * T / 2) - Real.cos θ)) := by
          gcongr

theorem solution :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ σ : ℝ, -1 < σ → σ < 1 →
        (∫ T : ℝ,
          stripPoissonKernel σ T * |T|) ≤ M := by
  have hpi2 : 0 < Real.pi / 2 := by positivity
  let g : ℝ → ℝ := fun T => (Icc (-1 : ℝ) 1).indicator (fun _ => (1 / 4 : ℝ)) T +
    2 * (|T| ^ 1 * Real.exp (-(Real.pi / 2) * |T|))
  have hg : Integrable g := by
    refine Integrable.add ?_ ((h47_int_abs_pow_exp 1 hpi2).const_mul 2)
    exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  refine ⟨∫ T, g T, integral_nonneg (fun T => ?_), ?_⟩
  · have : 0 ≤ (Icc (-1 : ℝ) 1).indicator (fun _ => (1 / 4 : ℝ)) T :=
      Set.indicator_nonneg (fun _ _ => by norm_num) T
    have := Real.exp_pos (-(Real.pi / 2) * |T|)
    simp only [g]; positivity
  intro σ h1 h2
  refine integral_mono_of_nonneg (Eventually.of_forall fun T => (h47_strip_pw h1 h2 T).1) hg
    (Eventually.of_forall fun T => ?_)
  have hp := h47_strip_pw h1 h2 T
  have he := Real.exp_pos (-(Real.pi / 2) * |T|)
  have hpos : 0 ≤ 2 * (|T| ^ 1 * Real.exp (-(Real.pi / 2) * |T|)) := by positivity
  simp only [g]
  by_cases hT : T ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hT]; linarith [hp.2.1]
  · rw [Set.indicator_of_notMem hT, zero_add]
    apply hp.2.2
    simp only [mem_Icc, not_and_or, not_le] at hT
    rcases hT with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

