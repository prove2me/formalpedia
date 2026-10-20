-- Prove2me | solution 2 for CohnElkies.stripNormalizedPoissonKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:28:29.23868+00:00
-- url     : https://prove2.me/submissions/6546dd2a-3b73-4e51-b913-a68efcf25018

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
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

theorem solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (stripNormalizedPoissonKernel σ) := by
  have hpi := Real.pi_pos
  set θ := Real.pi * (1 + σ) / 2 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; nlinarith
  have hθπ : θ < Real.pi := by rw [hθ]; nlinarith
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le hθπ.le
  have hc1 : Real.cos θ < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθπ.le hθ0
    simpa using h
  set m := min 1 (1 - Real.cos θ) with hm
  have hm0 : 0 < m := lt_min one_pos (by linarith)
  have hbound : ∀ T : ℝ, 0 ≤ stripPoissonKernel σ T ∧
      stripPoissonKernel σ T ≤ Real.sin θ / (2 * m) * Real.exp (-(Real.pi / 2) * |T|) := by
    intro T
    unfold stripPoissonKernel stripAngle
    rw [← hθ]
    have hC1 := Real.one_le_cosh (Real.pi * T / 2)
    have hlow : m * Real.cosh (Real.pi * T / 2) ≤ Real.cosh (Real.pi * T / 2) - Real.cos θ := by
      rcases le_total (Real.cos θ) 0 with h | h
      · have : m ≤ 1 := min_le_left _ _
        nlinarith
      · have : m ≤ 1 - Real.cos θ := min_le_right _ _
        nlinarith
    have hch : Real.exp (Real.pi / 2 * |T|) / 2 ≤ Real.cosh (Real.pi * T / 2) := by
      rw [← Real.cosh_abs, Real.cosh_eq]
      have : |Real.pi * T / 2| = Real.pi / 2 * |T| := by
        rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num; ring
      rw [this]
      linarith [Real.exp_pos (-(Real.pi / 2 * |T|))]
    have hG := Real.exp_pos (Real.pi / 2 * |T|)
    have hFG : Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi / 2 * |T|) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have hD0 : 0 < 4 * (Real.cosh (Real.pi * T / 2) - Real.cos θ) := by nlinarith
    refine ⟨div_nonneg hs hD0.le, ?_⟩
    rw [div_le_iff₀ hD0]
    have hD1 : 2 * m * Real.exp (Real.pi / 2 * |T|) ≤ 4 * (Real.cosh (Real.pi * T / 2) - Real.cos θ) := by
      nlinarith
    have hF := Real.exp_pos (-(Real.pi / 2) * |T|)
    calc Real.sin θ = Real.sin θ / (2 * m) * Real.exp (-(Real.pi / 2) * |T|) *
          (2 * m * Real.exp (Real.pi / 2 * |T|)) := by
          have h2m : (2 * m) ≠ 0 := by positivity
          rw [show Real.sin θ / (2 * m) * Real.exp (-(Real.pi / 2) * |T|) * (2 * m * Real.exp (Real.pi / 2 * |T|))
              = Real.sin θ * (Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi / 2 * |T|)) * ((2 * m) / (2 * m)) by ring,
            hFG, div_self h2m]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD1 (by positivity)
  have hmaj : Integrable (fun T : ℝ => Real.sin θ / (2 * m) * Real.exp (-(Real.pi / 2) * |T|)) := by
    refine ((h47_int_abs_pow_exp 0 (by positivity : (0:ℝ) < Real.pi / 2)).const_mul
      (Real.sin θ / (2 * m))).congr (Filter.Eventually.of_forall fun T => ?_)
    simp
  have hK : Integrable (fun T : ℝ => stripPoissonKernel σ T) := by
    have hmeas : Measurable (fun T : ℝ => stripPoissonKernel σ T) := by
      unfold stripPoissonKernel; fun_prop
    refine hmaj.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun T => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound T).1]
    exact (hbound T).2
  unfold stripNormalizedPoissonKernel
  exact hK.div_const _

