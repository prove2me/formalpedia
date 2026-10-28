-- Prove2me | solution 1 for EthierKurtz.gaussian_tail_variance_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:01:37.844822+00:00
-- url     : https://prove2.me/submissions/43b5c119-d644-42cc-a9c9-70ee61ce7ecc

import Mathlib.Tactic
import Mathlib
import Theorems.Thm_OAI_GaussianPropeller_Mills_inverse_mills_ratio_deriv_le_one
import Theorems.Thm_OAI_GaussianPropeller_Mills_gaussian_tail_le_sampford


open MeasureTheory Set

namespace TailAux

noncomputable def E (r : ℝ) : ℝ := Real.exp (-r^2/2)
noncomputable def T (r : ℝ) : ℝ := ∫ t in Set.Ioi r, Real.exp (-t^2/2)
noncomputable def H (r : ℝ) : ℝ := E r / T r

lemma integrable_E : Integrable (fun t : ℝ => Real.exp (-t^2/2)) := by
  have := integrable_exp_neg_mul_sq (b := 1/2) (by norm_num)
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only; congr 1; ring

lemma T_pos (r : ℝ) : 0 < T r := by
  unfold T
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun t => (Real.exp_pos _).le)
    integrable_E.integrableOn]
  have : Function.support (fun t : ℝ => Real.exp (-t^2/2)) = univ := by
    ext t; simp [(Real.exp_pos _).ne']
  rw [this, univ_inter, Real.volume_Ioi]; simp

lemma T_eq (r : ℝ) : T r = T 0 - ∫ t in (0:ℝ)..r, Real.exp (-t^2/2) := by
  unfold T
  rw [← intervalIntegral.integral_Ioi_sub_Ioi' integrable_E.integrableOn integrable_E.integrableOn]
  ring

lemma T_deriv (r : ℝ) : HasDerivAt T (-E r) r := by
  have h1 : HasDerivAt (fun u => ∫ t in (0:ℝ)..u, Real.exp (-t^2/2)) (Real.exp (-r^2/2)) r :=
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t^2/2)).integral_hasStrictDerivAt 0 r).hasDerivAt
  have h2 := h1.const_sub (T 0)
  have : T = fun u => T 0 - ∫ t in (0:ℝ)..u, Real.exp (-t^2/2) := funext T_eq
  rw [this]; simpa [E] using h2

lemma E_deriv (r : ℝ) : HasDerivAt E (-r * E r) r := by
  have h0 : HasDerivAt (fun x : ℝ => -x^2/2) (-r) r := by
    have := (hasDerivAt_pow 2 r).const_mul (-1/2 : ℝ)
    have e : (fun x:ℝ => -x^2/2) = fun y => -1/2 * y^2 := by ext; ring
    rw [e]; exact this.congr_deriv (by push_cast; ring)
  have := h0.exp
  show HasDerivAt (fun x => Real.exp (-x^2/2)) _ r
  exact this.congr_deriv (by simp only [E]; ring)

lemma H_deriv (r : ℝ) : HasDerivAt H (H r * (H r - r)) r := by
  have := (E_deriv r).div (T_deriv r) (T_pos r).ne'
  have hT := (T_pos r).ne'
  rw [show H = E / T from rfl]
  refine this.congr_deriv ?_
  simp only [Pi.div_apply]
  field_simp
  ring

lemma H_mul_le (r : ℝ) : H r * (H r - r) ≤ 1 :=
  OAI.GaussianPropeller.Mills.inverse_mills_ratio_deriv_le_one r

lemma H_ge {r : ℝ} (hr : 0 ≤ r) : r ≤ H r := by
  have hs := OAI.GaussianPropeller.Mills.gaussian_tail_le_sampford hr
  have hq : r ≤ Real.sqrt (r^2+8) := by
    exact (le_abs_self r).trans (Real.abs_le_sqrt (by nlinarith))
  have hK : 0 < (3*r + Real.sqrt (r^2+8))/4 := by
    have := Real.sqrt_pos.2 (show (0:ℝ) < r^2+8 by positivity); linarith
  have hT := T_pos r
  change T r ≤ E r / _ at hs
  rw [le_div_iff₀ hK] at hs
  unfold H; rw [le_div_iff₀ hT]; nlinarith

lemma H_le {r : ℝ} (hr : 0 ≤ r) : H r ≤ r + 1 := by
  have h1 := H_mul_le r; have h2 := H_ge hr
  by_contra h; push Not at h; nlinarith

lemma psi_eq (r : ℝ) : 1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) r
    = (√(2 * Real.pi))⁻¹ * T r := by
  rw [ProbabilityTheory.cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, compl_Iic,
    measureReal_def, ProbabilityTheory.gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun _ _ =>
      ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)]
  unfold T
  rw [← integral_const_mul]
  congr 1; ext t
  simp [ProbabilityTheory.gaussianPDFReal]


lemma taylor2 {f f1 f2 : ℝ → ℝ} {c M : ℝ}
    (hf : ∀ t, c ≤ t → HasDerivAt f (f1 t) t)
    (hf1 : ∀ t, c ≤ t → HasDerivAt f1 (f2 t) t)
    (hM : ∀ t, c ≤ t → |f2 t| ≤ M) {a v : ℝ} (ha : c ≤ a) (hv : c ≤ v) :
    |f v - f a - f1 a * (v - a)| ≤ M * (v - a)^2 / 2 := by
  have lip : ∀ p q, c ≤ p → p ≤ q → |f1 q - f1 p| ≤ M * (q - p) := by
    intro p q hp hpq
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f1) (f' := f2) (a := p) (b := q)
      (C := M) (fun t ht => (hf1 t (hp.trans ht.1)).hasDerivWithinAt)
      (fun t ht => by rw [Real.norm_eq_abs]; exact hM t (hp.trans ht.1)) q ⟨hpq, le_rfl⟩
    simpa [Real.norm_eq_abs] using this
  rcases le_total a v with hav | hva
  · have hF : ∀ t, c ≤ t → HasDerivAt (fun t => f t - f a - f1 a * (t - a)) (f1 t - f1 a) t := by
      intro t ht
      exact (((hf t ht).sub_const (f a)).sub (((hasDerivAt_id' t).sub_const a).const_mul (f1 a))).congr_deriv
        (by ring)
    have hB : ∀ t, HasDerivAt (fun t => M * (t - a)^2 / 2) (M * (t - a)) t := by
      intro t
      exact ((((hasDerivAt_id' t).sub_const a).pow 2).const_mul M).div_const 2 |>.congr_deriv
        (by push_cast; ring)
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun t => f t - f a - f1 a * (t - a)) (f' := fun t => f1 t - f1 a) (a := a) (b := v)
      (B := fun t => M * (t - a)^2 / 2) (B' := fun t => M * (t - a))
      (fun t ht => (hF t (ha.trans ht.1)).continuousAt.continuousWithinAt)
      (fun t ht => (hF t (ha.trans ht.1)).hasDerivWithinAt) (by simp) hB
      (fun t ht => by rw [Real.norm_eq_abs]; exact lip a t ha ht.1) ⟨hav, le_rfl⟩
    simpa [Real.norm_eq_abs] using this
  · have hG : ∀ t, t ≤ a - c → HasDerivAt (fun t => f (a - t) - f a + f1 a * t) (f1 a - f1 (a - t)) t := by
      intro t ht
      have h1 : HasDerivAt (fun t => f (a - t)) (f1 (a - t) * (-1)) t :=
        (hf (a - t) (by linarith)).comp t ((hasDerivAt_id' t).const_sub a |>.congr_deriv (by ring))
      exact ((h1.sub_const (f a)).add ((hasDerivAt_id' t).const_mul (f1 a))).congr_deriv (by ring)
    have hB : ∀ t, HasDerivAt (fun t => M * t^2 / 2) (M * t) t := by
      intro t
      exact (((hasDerivAt_id' t).pow 2).const_mul M).div_const 2 |>.congr_deriv
        (by push_cast; ring)
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun t => f (a - t) - f a + f1 a * t) (f' := fun t => f1 a - f1 (a - t)) (a := 0)
      (b := a - v) (B := fun t => M * t^2 / 2) (B' := fun t => M * t)
      (fun t ht => (hG t (by linarith [ht.2])).continuousAt.continuousWithinAt)
      (fun t ht => (hG t (by linarith [ht.2])).hasDerivWithinAt) (by simp) hB
      (fun t ht => by
        rw [Real.norm_eq_abs]
        have := lip (a - t) a (by linarith [ht.2]) (by linarith [ht.1])
        rw [show a - (a - t) = t by ring] at this; exact this)
      ⟨by linarith, le_rfl⟩
    simp only [Real.norm_eq_abs, sub_sub_cancel] at this
    calc |f v - f a - f1 a * (v - a)| = |f v - f a + f1 a * (a - v)| := by ring_nf
      _ ≤ M * (a - v)^2 / 2 := this
      _ = M * (v - a)^2 / 2 := by ring

noncomputable def F (x u : ℝ) : ℝ := Real.log (T (x / √u))
noncomputable def F1 (x u : ℝ) : ℝ := H (x / √u) * x / (2 * √u ^ 3)
noncomputable def F2 (x u : ℝ) : ℝ :=
  -(H (x / √u) * (H (x / √u) - x / √u)) * x ^ 2 / (4 * √u ^ 6) - 3 * H (x / √u) * x / (4 * √u ^ 5)

lemma r_deriv (x : ℝ) {u : ℝ} (hu : 0 < u) : HasDerivAt (fun u => x / √u) (-x / (2 * √u ^ 3)) u := by
  have hq := Real.sqrt_pos.2 hu
  have := (hasDerivAt_const u x).div (Real.hasDerivAt_sqrt hu.ne') hq.ne'
  exact this.congr_deriv (by field_simp; ring)

lemma F_deriv (x : ℝ) {u : ℝ} (hu : 0 < u) : HasDerivAt (F x) (F1 x u) u := by
  have hq := Real.sqrt_pos.2 hu
  have hT := T_pos (x / √u)
  have hc0 := (T_deriv (x / √u)).comp u (r_deriv x hu)
  have hc : HasDerivAt (fun y => T (x / √y)) (-E (x / √u) * (-x / (2 * √u ^ 3))) u := hc0
  have h := hc.log hT.ne'
  have h' : HasDerivAt (F x) _ u := h
  refine h'.congr_deriv ?_
  simp only [F1, H]
  field_simp

lemma F1_deriv (x : ℝ) {u : ℝ} (hu : 0 < u) : HasDerivAt (F1 x) (F2 x u) u := by
  have hq := Real.sqrt_pos.2 hu
  have h00 := (H_deriv (x / √u)).comp u (r_deriv x hu)
  have h0 : HasDerivAt (fun y => H (x / √y)) (H (x / √u) * (H (x / √u) - x / √u) * (-x / (2 * √u ^ 3))) u := h00
  have h1 := h0.mul_const x
  have h3 : HasDerivAt (fun y => √y ^ 3) ((3:ℕ) * √u ^ (3 - 1) * (1 / (2 * √u))) u :=
    (hasDerivAt_pow 3 (√u)).comp u (Real.hasDerivAt_sqrt hu.ne')
  have h2 := h3.const_mul 2
  have h := h1.div h2 (by positivity)
  have h' : HasDerivAt (F1 x) _ u := h
  refine h'.congr_deriv ?_
  simp only [F2]
  push_cast
  field_simp
  ring

lemma bound_aux {m q x A Hh r : ℝ} (hm : 0 < m) (hq : m ≤ q) (hx : 0 ≤ x) (hr : r = x / q)
    (h1 : 0 ≤ A) (h2 : A ≤ 1) (h3 : 0 ≤ Hh) (h4 : Hh ≤ r + 1) :
    |-A * x ^ 2 / (4 * q ^ 6) - 3 * Hh * x / (4 * q ^ 5)| ≤
      2 * (1 / m ^ 5 + 10 / m ^ 6) * (x ^ 2 + 1) := by
  have hq0 : 0 < q := hm.trans_le hq
  set p := 1 / q with hpdef
  set n := 1 / m with hndef
  have hp : 0 < p := by positivity
  have hpn : p ≤ n := one_div_le_one_div_of_le hm hq
  have hrp : r = x * p := by rw [hr, hpdef]; ring
  have key : -A * x ^ 2 / (4 * q ^ 6) - 3 * Hh * x / (4 * q ^ 5)
      = -(A * x ^ 2 * p ^ 6 + 3 * (Hh * x * p ^ 5)) / 4 := by
    rw [hpdef]; field_simp; ring
  have hM : 2 * (1 / m ^ 5 + 10 / m ^ 6) * (x ^ 2 + 1) = 2 * (n ^ 5 + 10 * n ^ 6) * (x ^ 2 + 1) := by
    rw [hndef]; field_simp
  rw [key, hM]
  have p6 : p ^ 6 ≤ n ^ 6 := pow_le_pow_left₀ hp.le hpn 6
  have p5 : p ^ 5 ≤ n ^ 5 := pow_le_pow_left₀ hp.le hpn 5
  have hn : 0 < n := by positivity
  have s1 : A * x ^ 2 * p ^ 6 ≤ x ^ 2 * n ^ 6 := by
    have a1 : A * (x ^ 2 * p ^ 6) ≤ 1 * (x ^ 2 * p ^ 6) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have a2 : x ^ 2 * p ^ 6 ≤ x ^ 2 * n ^ 6 := mul_le_mul_of_nonneg_left p6 (by positivity)
    nlinarith
  have s2 : Hh * x * p ^ 5 ≤ x ^ 2 * n ^ 6 + x * n ^ 5 := by
    have a1 : Hh * (x * p ^ 5) ≤ (x * p + 1) * (x * p ^ 5) :=
      mul_le_mul_of_nonneg_right (hrp ▸ h4) (by positivity)
    have a2 : x ^ 2 * p ^ 6 ≤ x ^ 2 * n ^ 6 := mul_le_mul_of_nonneg_left p6 (by positivity)
    have a3 : x * p ^ 5 ≤ x * n ^ 5 := mul_le_mul_of_nonneg_left p5 hx
    nlinarith
  have s0 : 0 ≤ A * x ^ 2 * p ^ 6 + 3 * (Hh * x * p ^ 5) := by positivity
  have s3 : x * n ^ 5 ≤ (x ^ 2 + 1) * n ^ 5 :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have s4 : 0 ≤ n ^ 6 * (x ^ 2 + 1) := by positivity
  have s5 : x ^ 2 * n ^ 6 ≤ n ^ 6 * (x ^ 2 + 1) := by nlinarith
  rw [abs_le]; constructor <;> nlinarith

lemma F2_bound {m x u : ℝ} (hm : 0 < m) (hx : 0 ≤ x) (hu : m ^ 2 ≤ u) :
    |F2 x u| ≤ 2 * (1 / m ^ 5 + 10 / m ^ 6) * (x ^ 2 + 1) := by
  have hq : m ≤ √u := by
    have := Real.abs_le_sqrt hu; rwa [abs_of_pos hm] at this
  have hq0 : 0 < √u := hm.trans_le hq
  have hr : 0 ≤ x / √u := by positivity
  have hg := H_ge hr
  have hl := H_le hr
  have hA := H_mul_le (x / √u)
  unfold F2
  exact bound_aux hm hq hx rfl (by nlinarith) hA (by linarith) hl

end TailAux

open TailAux in
theorem solution :
    ∀ {m s sp x : ℝ},
      (0 : ℝ) < m →
        m ≤ s →
          m ≤ sp →
            (0 : ℝ) ≤ x →
              (1 : ℝ) - (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / sp) ≤
                  ((1 : ℝ) - (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / s)) *
                    Real.exp
                      ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-((x / s) ^ (2 : ℕ) / (2 : ℝ))) /
                                ((1 : ℝ) -
                                  (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / s)) *
                              x /
                            ((2 : ℝ) * s ^ (3 : ℕ)) *
                          (sp ^ (2 : ℕ) - s ^ (2 : ℕ)) +
                        ((1 : ℝ) / m ^ (5 : ℕ) + (10 : ℝ) / m ^ (6 : ℕ)) * (x ^ (2 : ℕ) + (1 : ℝ)) *
                          (sp ^ (2 : ℕ) - s ^ (2 : ℕ)) ^ (2 : ℕ)) ∧
                ((1 : ℝ) - (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / s)) *
                    Real.exp
                      ((√((2 : ℝ) * Real.pi))⁻¹ * Real.exp (-((x / s) ^ (2 : ℕ) / (2 : ℝ))) /
                                ((1 : ℝ) -
                                  (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / s)) *
                              x /
                            ((2 : ℝ) * s ^ (3 : ℕ)) *
                          (sp ^ (2 : ℕ) - s ^ (2 : ℕ)) -
                        ((1 : ℝ) / m ^ (5 : ℕ) + (10 : ℝ) / m ^ (6 : ℕ)) * (x ^ (2 : ℕ) + (1 : ℝ)) *
                          (sp ^ (2 : ℕ) - s ^ (2 : ℕ)) ^ (2 : ℕ)) ≤
                  (1 : ℝ) - (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) (x / sp) := by
  intro m s sp x hm hs hsp hx
  have hs0 : 0 < s := hm.trans_le hs
  have hsp0 : 0 < sp := hm.trans_le hsp
  have hTs := T_pos (x / s)
  have hTsp := T_pos (x / sp)
  set c : ℝ := (√((2 : ℝ) * Real.pi))⁻¹ with hc
  have hc0 : 0 < c := by positivity
  set R := ((1 : ℝ) / m ^ 5 + 10 / m ^ 6) * (x ^ 2 + 1) * (sp ^ 2 - s ^ 2) ^ 2 with hR
  have hfirst : c * Real.exp (-((x / s) ^ 2 / 2)) / (c * T (x / s)) * x / (2 * s ^ 3)
      * (sp ^ 2 - s ^ 2) = F1 x (s ^ 2) * (sp ^ 2 - s ^ 2) := by
    simp only [F1, H, E, Real.sqrt_sq hs0.le]
    rw [show -((x / s) ^ 2 / 2) = -(x / s) ^ 2 / 2 by ring]
    field_simp
  have hm2 : 0 < m ^ 2 := by positivity
  have hty := taylor2 (c := m ^ 2) (f := F x) (f1 := F1 x) (f2 := F2 x)
    (M := 2 * (1 / m ^ 5 + 10 / m ^ 6) * (x ^ 2 + 1))
    (fun t ht => F_deriv x (hm2.trans_le ht)) (fun t ht => F1_deriv x (hm2.trans_le ht))
    (fun t ht => F2_bound hm hx ht) (a := s ^ 2) (v := sp ^ 2)
    (pow_le_pow_left₀ hm.le hs 2) (pow_le_pow_left₀ hm.le hsp 2)
  rw [show 2 * (1 / m ^ 5 + 10 / m ^ 6) * (x ^ 2 + 1) * (sp ^ 2 - s ^ 2) ^ 2 / 2 = R by
    rw [hR]; ring] at hty
  have hratio : T (x / sp) = T (x / s) * Real.exp (F x (sp ^ 2) - F x (s ^ 2)) := by
    rw [Real.exp_sub, F, F, Real.sqrt_sq hs0.le, Real.sqrt_sq hsp0.le, Real.exp_log hTs,
      Real.exp_log hTsp]
    field_simp
  rw [abs_le] at hty
  rw [psi_eq (x / sp), psi_eq (x / s), hfirst, hratio]
  constructor
  · rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
  · rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
