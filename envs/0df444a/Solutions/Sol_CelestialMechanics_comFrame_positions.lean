-- Prove2me | solution 1 for CelestialMechanics.comFrame_positions
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T19:37:45.695007+00:00
-- url     : https://prove2.me/submissions/d1ceb5f8-f45a-4562-b307-a82f6e84163d

import Mathlib
import Definitions.Def_CelestialMechanics_binary_star_dynamics

open CelestialMechanics

theorem W2c_CelestialMechanics_com (m₁ m₂ : ℝ) (r₁ r₂ : ℝ → Space)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hcom : ∀ t, m₁ • r₁ t + m₂ • r₂ t = 0) :
    (∀ t, r₁ t = (-(m₂ / (m₁ + m₂))) • (r₂ t - r₁ t)) ∧
    (∀ t, r₂ t = (m₁ / (m₁ + m₂)) • (r₂ t - r₁ t)) := by
  have hM : m₁ + m₂ ≠ 0 := (add_pos hm₁ hm₂).ne'
  constructor
  · intro t
    ext i
    have := congrArg (fun v : Space => v i) (hcom t)
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at this
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    linarith
  · intro t
    ext i
    have := congrArg (fun v : Space => v i) (hcom t)
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at this
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    linarith

theorem W2c_CelestialMechanics_masses (G m₁ m₂ a T : ℝ) (r₁ r₂ : ℝ → Space)
    (hG : 0 < G) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (ha : 0 < a) (hT : 0 < T)
    (hper : T = Real.sqrt (4 * Real.pi ^ 2 * a ^ 3 / (G * (m₁ + m₂))))
    (hcom : ∀ t, m₁ • r₁ t + m₂ • r₂ t = 0) :
    m₁ + m₂ = 4 * Real.pi ^ 2 * a ^ 3 / (G * T ^ 2) ∧
    ∀ t, m₁ * ‖r₁ t‖ = m₂ * ‖r₂ t‖ := by
  have hMpos : 0 < m₁ + m₂ := add_pos hm₁ hm₂
  have hπ := Real.pi_pos
  have hT2 : T ^ 2 = 4 * Real.pi ^ 2 * a ^ 3 / (G * (m₁ + m₂)) := by
    rw [hper, Real.sq_sqrt (by positivity)]
  refine ⟨?_, fun t => ?_⟩
  · rw [hT2]
    have : a ≠ 0 := ha.ne'
    have : G ≠ 0 := hG.ne'
    have : Real.pi ≠ 0 := hπ.ne'
    have : m₁ + m₂ ≠ 0 := hMpos.ne'
    field_simp
  · have h := hcom t
    have h2 : m₁ • r₁ t = -(m₂ • r₂ t) := eq_neg_of_add_eq_zero_left h
    have h3 := congrArg norm h2
    rw [norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg hm₁.le,
      Real.norm_of_nonneg hm₂.le] at h3
    exact h3

theorem W2c_CelestialMechanics_uniform (G m₁ m₂ : ℝ) (r₁ r₂ : ℝ → Space)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h : IsNewtonianTwoBody G m₁ m₂ r₁ r₂) :
    ∃ R₀ V : Space, ∀ t, centerOfMass m₁ m₂ r₁ r₂ t = R₀ + t • V := by
  obtain ⟨h1, h2, _, e1, e2⟩ := h
  have d1 : Differentiable ℝ r₁ := h1.differentiable (by norm_num)
  have d2 : Differentiable ℝ r₂ := h2.differentiable (by norm_num)
  have dd1 : Differentiable ℝ (deriv r₁) := (h1.iterate_deriv' 1 1).differentiable (by norm_num)
  have dd2 : Differentiable ℝ (deriv r₂) := (h2.iterate_deriv' 1 1).differentiable (by norm_num)
  have hsum : ∀ t, m₁ • deriv (deriv r₁) t + m₂ • deriv (deriv r₂) t = 0 := by
    intro t
    have a1 := e1 t
    have a2 := e2 t
    rw [iteratedDeriv_succ, iteratedDeriv_one] at a1 a2
    rw [a1, a2, ← add_smul]
    have : G * m₁ * m₂ / ‖r₂ t - r₁ t‖ ^ 3 + -(G * m₁ * m₂) / ‖r₂ t - r₁ t‖ ^ 3 = 0 := by
      ring
    rw [this, zero_smul]
  let V : ℝ → Space := fun t =>
    (m₁ / (m₁ + m₂)) • deriv r₁ t + (m₂ / (m₁ + m₂)) • deriv r₂ t
  have hV : ∀ t, HasDerivAt V ((m₁ / (m₁ + m₂)) • deriv (deriv r₁) t +
      (m₂ / (m₁ + m₂)) • deriv (deriv r₂) t) t :=
    fun t => ((dd1 t).hasDerivAt.const_smul (m₁ / (m₁ + m₂))).add
      ((dd2 t).hasDerivAt.const_smul (m₂ / (m₁ + m₂)))
  have hV0 : ∀ t, (m₁ / (m₁ + m₂)) • deriv (deriv r₁) t +
      (m₂ / (m₁ + m₂)) • deriv (deriv r₂) t = 0 := by
    intro t
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm m₁, mul_comm m₂, mul_smul, mul_smul,
      ← smul_add, hsum t, smul_zero]
  have hVc : ∀ t, V t = V 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hV s).differentiableAt)
      (fun s => (hV s).deriv.trans (hV0 s)) t 0
  have hC : ∀ t, HasDerivAt (centerOfMass m₁ m₂ r₁ r₂) (V t) t :=
    fun t => ((d1 t).hasDerivAt.const_smul (m₁ / (m₁ + m₂))).add
      ((d2 t).hasDerivAt.const_smul (m₂ / (m₁ + m₂)))
  have hW : ∀ t, HasDerivAt (fun s => centerOfMass m₁ m₂ r₁ r₂ s - s • V 0)
      (V t - (1:ℝ) • V 0) t :=
    fun t => (hC t).sub ((hasDerivAt_id' t).smul_const (V 0))
  refine ⟨centerOfMass m₁ m₂ r₁ r₂ 0, V 0, fun t => ?_⟩
  have := is_const_of_deriv_eq_zero (fun s => (hW s).differentiableAt)
    (fun s => by rw [(hW s).deriv, hVc s, one_smul, sub_self]) t 0
  simp only [zero_smul, sub_zero] at this
  rw [← this]
  abel

theorem W2c_CelestialMechanics_reduction (G m₁ m₂ : ℝ) (r₁ r₂ : ℝ → Space)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h : IsNewtonianTwoBody G m₁ m₂ r₁ r₂) :
    IsKeplerRelative G (m₁ + m₂) (fun t => r₂ t - r₁ t) := by
  obtain ⟨h1, h2, hne, e1, e2⟩ := h
  refine ⟨h2.sub h1, fun t => sub_ne_zero.2 (hne t).symm, fun t => ?_⟩
  have a1 : iteratedDeriv 2 r₁ t = (G * m₂ / ‖r₂ t - r₁ t‖ ^ 3) • (r₂ t - r₁ t) := by
    have h3 := congrArg (fun v => m₁⁻¹ • v) (e1 t)
    simp only [smul_smul, inv_mul_cancel₀ hm₁.ne', one_smul] at h3
    rw [h3]
    congr 1
    field_simp
  have a2 : iteratedDeriv 2 r₂ t = (-(G * m₁) / ‖r₂ t - r₁ t‖ ^ 3) • (r₂ t - r₁ t) := by
    have h3 := congrArg (fun v => m₂⁻¹ • v) (e2 t)
    simp only [smul_smul, inv_mul_cancel₀ hm₂.ne', one_smul] at h3
    rw [h3]
    congr 1
    field_simp
  show iteratedDeriv 2 (r₂ - r₁) t =
    (-(G * (m₁ + m₂)) / ‖r₂ t - r₁ t‖ ^ 3) • (r₂ t - r₁ t)
  rw [iteratedDeriv_sub h2.contDiffAt h1.contDiffAt, a1, a2, ← sub_smul]
  congr 1
  ring

theorem W2c_CelestialMechanics_kepler (G M a e h : ℝ) (rad th : ℝ → ℝ) (r : ℝ → Space)
    (hG : 0 < G) (hM : 0 < M) (ha : 0 < a) (he0 : 0 ≤ e) (he1 : e < 1)
    (hh : 0 < h) (hha : h ^ 2 = (1 - e ^ 2) * G * M * a)
    (horb : IsConicOrbit a e h rad th r) :
    IsKeplerRelative G M r := by
  obtain ⟨hthd, hrad, hthr, hr0, hr1, hr2⟩ := horb
  have h1e : 0 < 1 - e ^ 2 := by nlinarith
  set p := a * (1 - e ^ 2) with hp
  have hp0 : 0 < p := mul_pos ha h1e
  have hden : ∀ u : ℝ, 0 < 1 + e * Real.cos u := by
    intro u
    nlinarith [mul_le_mul_of_nonneg_left (Real.neg_one_le_cos u) he0]
  have hradpos : ∀ t, 0 < rad t := fun t => by rw [hrad t]; exact div_pos hp0 (hden _)
  have hth' : ∀ t, HasDerivAt th (h * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2) t := by
    intro t
    have := (hthd t).hasDerivAt
    rw [hthr t, hrad t] at this
    have hd := (hden (th t)).ne'
    refine this.congr_deriv ?_
    field_simp
  have hF1 : ContDiff ℝ 1 (fun u : ℝ => h * (1 + e * Real.cos u) ^ 2 / p ^ 2) :=
    (contDiff_const.mul ((contDiff_const.add (contDiff_const.mul Real.contDiff_cos)).pow
      2)).div_const _
  have hdth : deriv th = (fun u : ℝ => h * (1 + e * Real.cos u) ^ 2 / p ^ 2) ∘ th :=
    funext fun t => (hth' t).deriv
  have hθd : Differentiable ℝ th := hthd
  have hθ1 : ContDiff ℝ 1 th := contDiff_one_iff_deriv.2
    ⟨hθd, by rw [hdth]; exact hF1.continuous.comp hθd.continuous⟩
  have hθ2 : ContDiff ℝ 2 th := by
    have : ContDiff ℝ 1 (deriv th) := by rw [hdth]; exact hF1.comp hθ1
    rw [← one_add_one_eq_two]
    exact contDiff_succ_iff_deriv.2 ⟨hθd, by simp, this⟩
  let X : ℝ → ℝ := fun t => p * Real.cos (th t) / (1 + e * Real.cos (th t))
  let Y : ℝ → ℝ := fun t => p * Real.sin (th t) / (1 + e * Real.cos (th t))
  let E0 : Space := EuclideanSpace.single 0 1
  let E1 : Space := EuclideanSpace.single 1 1
  have hrfun : r = fun t => X t • E0 + Y t • E1 := by
    funext t
    ext i
    fin_cases i <;> simp [X, Y, E0, E1, hr0, hr1, hr2, hrad] <;> ring
  have hX : ∀ t, HasDerivAt X (-(h / p) * Real.sin (th t)) t := by
    intro t
    have hc := (hth' t).cos
    have h1 := (hc.const_mul p).div ((hc.const_mul e).const_add 1) (hden (th t)).ne'
    have hd := (hden (th t)).ne'
    refine h1.congr_deriv ?_
    field_simp
    ring
  have hY : ∀ t, HasDerivAt Y ((h / p) * (e + Real.cos (th t))) t := by
    intro t
    have hc := (hth' t).cos
    have hs := (hth' t).sin
    have h1 := (hs.const_mul p).div ((hc.const_mul e).const_add 1) (hden (th t)).ne'
    have hd := (hden (th t)).ne'
    refine h1.congr_deriv ?_
    field_simp
    ring_nf
    rw [Real.sin_sq]
    have hd' : 1 + Real.cos (th t) * e ≠ 0 := by rw [mul_comm]; exact hd
    field_simp
    ring
  have hX' : ∀ t, HasDerivAt (fun s => -(h / p) * Real.sin (th s))
      (-(h / p) * (Real.cos (th t) * (h * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2))) t :=
    fun t => (hth' t).sin.const_mul _
  have hY' : ∀ t, HasDerivAt (fun s => (h / p) * (e + Real.cos (th s)))
      ((h / p) * (-Real.sin (th t) * (h * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2))) t :=
    fun t => ((hth' t).cos.const_add e).const_mul _
  have hr' : ∀ t, HasDerivAt r ((-(h / p) * Real.sin (th t)) • E0 +
      ((h / p) * (e + Real.cos (th t))) • E1) t := by
    intro t; rw [hrfun]; exact ((hX t).smul_const E0).add ((hY t).smul_const E1)
  have hdr : deriv r = fun t => (-(h / p) * Real.sin (th t)) • E0 +
      ((h / p) * (e + Real.cos (th t))) • E1 := funext fun t => (hr' t).deriv
  have hr'' : ∀ t, HasDerivAt (deriv r)
      ((-(h / p) * (Real.cos (th t) * (h * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2))) • E0 +
      ((h / p) * (-Real.sin (th t) * (h * (1 + e * Real.cos (th t)) ^ 2 / p ^ 2))) • E1)
      t := by
    intro t; rw [hdr]; exact ((hX' t).smul_const E0).add ((hY' t).smul_const E1)
  have hnorm : ∀ t, ‖r t‖ = rad t := by
    intro t
    have e : ‖rad t * Real.cos (th t)‖ ^ 2 + ‖rad t * Real.sin (th t)‖ ^ 2 + ‖(0:ℝ)‖ ^ 2
        = rad t ^ 2 := by
      simp only [Real.norm_eq_abs, sq_abs]
      linear_combination (rad t) ^ 2 * Real.sin_sq_add_cos_sq (th t)
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, hr0, hr1, hr2, e,
      Real.sqrt_sq (hradpos t).le]
  have hXc : ContDiff ℝ 2 X :=
    (contDiff_const.mul (Real.contDiff_cos.comp hθ2)).div
      (contDiff_const.add (contDiff_const.mul (Real.contDiff_cos.comp hθ2)))
      (fun t => (hden _).ne')
  have hYc : ContDiff ℝ 2 Y :=
    (contDiff_const.mul (Real.contDiff_sin.comp hθ2)).div
      (contDiff_const.add (contDiff_const.mul (Real.contDiff_cos.comp hθ2)))
      (fun t => (hden _).ne')
  have hGM : G * M = h ^ 2 / p := by
    rw [hha, hp]
    have : a ≠ 0 := ha.ne'
    have : 1 - e ^ 2 ≠ 0 := h1e.ne'
    field_simp
  refine ⟨?_, fun t => ?_, fun t => ?_⟩
  · rw [hrfun]
    exact (hXc.smul contDiff_const).add (hYc.smul contDiff_const)
  · intro h0
    have := hnorm t
    rw [h0, norm_zero] at this
    linarith [hradpos t]
  · rw [iteratedDeriv_succ, iteratedDeriv_one, (hr'' t).deriv, hnorm t, neg_div, hGM]
    have hd := (hden (th t)).ne'
    have hp' := hp0.ne'
    conv_rhs => rw [hrfun]
    ext i
    fin_cases i <;> simp [X, Y, E0, E1, hrad] <;> field_simp <;> ring

theorem solution (m₁ m₂ : ℝ) (r₁ r₂ : ℝ → Space)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hcom : ∀ t, m₁ • r₁ t + m₂ • r₂ t = 0) :
    (∀ t, r₁ t = (-(m₂ / (m₁ + m₂))) • (r₂ t - r₁ t)) ∧
    (∀ t, r₂ t = (m₁ / (m₁ + m₂)) • (r₂ t - r₁ t)) := by
  apply W2c_CelestialMechanics_com <;> assumption
