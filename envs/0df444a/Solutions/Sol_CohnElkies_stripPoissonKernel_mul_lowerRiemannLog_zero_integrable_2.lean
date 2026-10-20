-- Prove2me | solution 2 for CohnElkies.stripPoissonKernel_mul_lowerRiemannLog_zero_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:37:44.218273+00:00
-- url     : https://prove2.me/submissions/c6d45c31-708f-48bb-bb58-8ca1624fc431

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
theorem h47b_rpow_exp {s : ℝ} (hs : -1 < s) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun T : ℝ => |T| ^ s * Real.exp (-a * |T|)) := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s) (p := 1) (b := a) hs one_pos ha
  have hIoi : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ s * Real.exp (-a * |T|)) (Set.Ioi 0) := by
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := hx
    simp [abs_of_pos hx0]
  have hIio : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ s * Real.exp (-a * |T|)) (Set.Iio 0) := by
    have := (show MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ s * Real.exp (-a * |T|)) (Set.Ioi (-0)) by
      simpa using hIoi).comp_neg_Iio
    simpa [abs_neg] using this
  have hall : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ s * Real.exp (-a * |T|)) (Set.Iic 0 ∪ Set.Ioi 0) :=
    ((integrableOn_Iic_iff_integrableOn_Iio (b := (0:ℝ))).mpr hIio).union hIoi
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at hall
  exact hall

theorem h47b_le {x : ℝ} (hx : 0 < x) :
    |Real.log (lowerCoth (Real.pi * x) / x)| ≤
      2 * (Real.pi * x) +
        |Real.log Real.pi| + 2 * |Real.log x| := by
  have hpi := Real.pi_pos
  have hy : 0 < Real.pi * x := mul_pos hpi hx
  unfold lowerCoth
  have hs : 0 < Real.sinh (Real.pi * x) := Real.sinh_pos_iff.2 hy
  have hcs : Real.sinh (Real.pi * x) ≤ Real.cosh (Real.pi * x) := (Real.sinh_lt_cosh _).le
  have hc1 : 1 ≤ Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x) := (one_le_div hs).2 hcs
  have hcu : Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x) ≤ (Real.pi * x + 1) / (Real.pi * x) := by
    rw [div_le_div_iff₀ hs hy, Real.cosh_eq, Real.sinh_eq]
    have hE := Real.exp_pos (Real.pi * x)
    have hF := Real.exp_pos (-(Real.pi * x))
    have hEF : Real.exp (Real.pi * x) * Real.exp (-(Real.pi * x)) = 1 := by rw [← Real.exp_add]; simp
    have h2 : 2 * (Real.pi * x) + 1 ≤ Real.exp (Real.pi * x) * Real.exp (Real.pi * x) := by
      rw [← Real.exp_add]; linarith [Real.add_one_le_exp (Real.pi * x + Real.pi * x)]
    have h3 : Real.exp (Real.pi * x) * Real.exp (Real.pi * x) * Real.exp (-(Real.pi * x)) = Real.exp (Real.pi * x) := by
      rw [mul_assoc, hEF, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left h2 hF.le, mul_pos hF hy]
  have hlogc : Real.log (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) ≤ Real.pi * x - Real.log Real.pi - Real.log x := by
    have h1 := Real.log_le_log (by linarith) hcu
    rw [Real.log_div (by linarith) hy.ne', Real.log_mul hpi.ne' hx.ne'] at h1
    have h2 : Real.log (Real.pi * x + 1) ≤ Real.pi * x := by
      have := Real.log_le_sub_one_of_pos (show 0 < Real.pi * x + 1 by linarith); linarith
    linarith
  have hlogc0 : 0 ≤ Real.log (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) := Real.log_nonneg hc1
  rw [Real.log_div (by linarith) hx.ne', abs_le]
  constructor <;> linarith [le_abs_self (Real.log Real.pi), neg_abs_le (Real.log Real.pi), le_abs_self (Real.log x), neg_abs_le (Real.log x)]

theorem h47b_abslog {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ t + 2 * t ^ (-(1/2 : ℝ)) := by
  have hr : 0 < t ^ (-(1/2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have h1 := Real.log_le_sub_one_of_pos ht
  have h2 := Real.log_le_sub_one_of_pos hr
  rw [Real.log_rpow ht] at h2
  rw [abs_le]; constructor <;> nlinarith


theorem h47_strip_bound {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ stripPoissonKernel σ T ∧
      stripPoissonKernel σ T ≤ C * Real.exp (-(Real.pi / 2) * |T|) := by
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
  refine ⟨Real.sin θ / (2 * m), by positivity, fun T => hbound T⟩

theorem solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * lowerRiemannLog T 0) := by
  obtain ⟨C, hC0, hK⟩ := h47_strip_bound hbelow habove
  have hpi := Real.pi_pos
  have hmaj : Integrable (fun T : ℝ => Real.exp (-(Real.pi / 2) * |T|) *
      ((C * Real.log 2) + C * |T| + (2 * C) * |T| ^ (-(1/2 : ℝ)))) := by
    have h0 := (h47b_rpow_exp (s := 0) (by norm_num) (by positivity : (0:ℝ) < Real.pi / 2)).const_mul (C * Real.log 2)
    have h1 := (h47b_rpow_exp (s := 1) (by norm_num) (by positivity : (0:ℝ) < Real.pi / 2)).const_mul C
    have h2 := (h47b_rpow_exp (s := -(1/2 : ℝ)) (by norm_num) (by positivity : (0:ℝ) < Real.pi / 2)).const_mul (2 * C)
    refine ((h0.add h1).add h2).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, Real.rpow_zero, Real.rpow_one]
    ring
  have hmeas : Measurable (fun T : ℝ => stripPoissonKernel σ T * lowerRiemannLog T 0) := by
    unfold stripPoissonKernel lowerRiemannLog; fun_prop
  refine hmaj.mono' hmeas.aestronglyMeasurable ?_
  have hae : ∀ᵐ y : ℝ, y ≠ 0 := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hae] with T hT
  have hTp : 0 < |T| := abs_pos.mpr hT
  have hl : lowerRiemannLog T 0 = Real.log (|T| / 2) := by
    unfold lowerRiemannLog
    rw [show (0:ℝ) ^ 2 + T ^ 2 / 4 = (|T| / 2) ^ 2 by rw [div_pow, sq_abs]; ring,
      Real.sqrt_sq (by positivity)]
  rw [hl, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK T).1]
  have hlog : |Real.log (|T| / 2)| ≤ Real.log 2 + |T| + 2 * |T| ^ (-(1/2 : ℝ)) := by
    rw [Real.log_div hTp.ne' (by norm_num)]
    have h1 := h47b_abslog hTp
    have h2 := abs_sub (Real.log |T|) (Real.log 2)
    rw [abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 2))] at h2
    linarith
  have hE := Real.exp_pos (-(Real.pi / 2) * |T|)
  calc stripPoissonKernel σ T * |Real.log (|T| / 2)|
      ≤ C * Real.exp (-(Real.pi / 2) * |T|) * (Real.log 2 + |T| + 2 * |T| ^ (-(1/2 : ℝ))) :=
        mul_le_mul (hK T).2 hlog (abs_nonneg _) (by positivity)
    _ = _ := by ring

