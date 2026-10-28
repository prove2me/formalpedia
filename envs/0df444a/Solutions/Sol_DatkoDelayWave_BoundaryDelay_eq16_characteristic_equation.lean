-- Prove2me | solution 1 for DatkoDelayWave.BoundaryDelay.eq16_characteristic_equation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:01.690149+00:00
-- url     : https://prove2.me/submissions/570dbc04-1cb2-4fe8-9604-2bb360ecf372

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

-- carved verbatim out of submission 9e78ff97-3a87-4a96-9f66-6a86542faea0, lines 515-574

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
open Complex
open DatkoDelayWave
open DatkoDelayWave.BoundaryDelay
open Set Filter Metric
open scoped Topology

theorem key_identity (a k ε : ℝ) (ω : ℂ) :
    ((a : ℂ) + ω) * Complex.cosh ((a : ℂ) + ω)
      + (k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω) * Complex.sinh ((a : ℂ) + ω)
      = Complex.exp ((a : ℂ) + ω) / 2 * h a k ε ω := by
  have hK : (K a : ℂ) = Complex.exp (-2 * (a : ℂ)) := by
    unfold K; rw [Complex.ofReal_exp]; push_cast; ring_nf
  have hq : Complex.exp (-((a : ℂ) + ω))
      = Complex.exp ((a : ℂ) + ω) * ((K a : ℂ) * Complex.exp (-2 * ω)) := by
    rw [hK, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  unfold h f
  simp only [Complex.cosh, Complex.sinh]
  rw [hq]
  ring

theorem const_of_hasDeriv_zero (V V' : ℝ → ℂ) (hV : ∀ x, HasDerivAt V (V' x) x)
    (h0 : ∀ x ∈ Icc (0 : ℝ) 1, V' x = 0) : ∀ x ∈ Icc (0 : ℝ) 1, V x = V 0 := by
  apply constant_of_derivWithin_zero
  · intro x _; exact (hV x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hx
    rw [((hV x).hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc zero_lt_one x hx')]
    exact h0 x hx'

theorem eig_explicit (a k ε : ℝ) (ω : ℂ) (φ : ℝ → ℂ) (hφ : IsEigenpair a k ε ω φ) :
    ∀ x ∈ Icc (0 : ℝ) 1, deriv φ x = deriv φ 0 * Complex.cosh (((a : ℂ) + ω) * x) ∧
      ((a : ℂ) + ω) * φ x = deriv φ 0 * Complex.sinh (((a : ℂ) + ω) * x) := by
  set l : ℂ := (a : ℂ) + ω with hl
  have hC2 : ContDiff ℝ 2 φ := hφ.contDiff
  have hd1 : Differentiable ℝ φ := hC2.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv φ) := hC2.differentiable_deriv_two
  have hC1 : ContDiff ℝ 1 (deriv φ) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) φ from hC2)).2.2
  have hcdd : Continuous (deriv (deriv φ)) := hC1.continuous_deriv_one
  have hode : ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv φ) x = l ^ 2 * φ x := by
    have hEq : EqOn (deriv (deriv φ)) (fun x => l ^ 2 * φ x) (Ioo 0 1) := hφ.ode
    exact hEq.of_subset_closure hcdd.continuousOn
      (continuous_const.mul hd1.continuous).continuousOn Ioo_subset_Icc_self
      (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)])
  have hlin : ∀ x : ℝ, HasDerivAt (fun x : ℝ => l * (x : ℂ)) l x := by
    intro x
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul l
  have hch : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.cosh (l * (x : ℂ)))
      (Complex.sinh (l * (x : ℂ)) * l) x := fun x => by
    have := (Complex.hasDerivAt_cosh (l * (x : ℂ))).scomp x (hlin x)
    exact this.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hsh : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.sinh (l * (x : ℂ)))
      (Complex.cosh (l * (x : ℂ)) * l) x := fun x => by
    have := (Complex.hasDerivAt_sinh (l * (x : ℂ))).scomp x (hlin x)
    exact this.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hp1 : ∀ x : ℝ, HasDerivAt φ (deriv φ x) x := fun x => (hd1 x).hasDerivAt
  have hp2 : ∀ x : ℝ, HasDerivAt (deriv φ) (deriv (deriv φ) x) x := fun x => (hdd x).hasDerivAt
  have hV := const_of_hasDeriv_zero
    (fun x => deriv φ x * Complex.cosh (l * (x : ℂ)) - l * φ x * Complex.sinh (l * (x : ℂ)))
    (fun x => (deriv (deriv φ) x - l ^ 2 * φ x) * Complex.cosh (l * (x : ℂ)))
    (by
      intro x
      have := ((hp2 x).mul (hch x)).sub (((hp1 x).const_mul l).mul (hsh x))
      exact this.congr_deriv (by ring))
    (by intro x hx; rw [hode x hx]; ring)
  have hW := const_of_hasDeriv_zero
    (fun x => deriv φ x * Complex.sinh (l * (x : ℂ)) - l * φ x * Complex.cosh (l * (x : ℂ)))
    (fun x => (deriv (deriv φ) x - l ^ 2 * φ x) * Complex.sinh (l * (x : ℂ)))
    (by
      intro x
      have := ((hp2 x).mul (hsh x)).sub (((hp1 x).const_mul l).mul (hch x))
      exact this.congr_deriv (by ring))
    (by intro x hx; rw [hode x hx]; ring)
  intro x hx
  have hV0 := hV x hx
  have hW0 := hW x hx
  simp only [Complex.ofReal_zero, mul_zero, Complex.cosh_zero, Complex.sinh_zero, mul_one,
    hφ.left, sub_zero, zero_mul] at hV0 hW0
  have hsq := Complex.cosh_sq (l * (x : ℂ))
  constructor
  · linear_combination (Complex.cosh (l * (x : ℂ))) * hV0 - (Complex.sinh (l * (x : ℂ))) * hW0
      - (deriv φ x) * hsq
  · linear_combination (Complex.sinh (l * (x : ℂ))) * hV0 - (Complex.cosh (l * (x : ℂ))) * hW0
      - (l * φ x) * hsq

theorem sinh_lx_ne_zero (l : ℂ) (hl : l ≠ 0) :
    Complex.sinh (l * ((1 / (‖l‖ + 1) : ℝ) : ℂ)) ≠ 0 := by
  intro h0
  have hn : 0 < ‖l‖ := norm_pos_iff.mpr hl
  have hx : 0 < 1 / (‖l‖ + 1) := by positivity
  have hs : Complex.sin ((l * ((1 / (‖l‖ + 1) : ℝ) : ℂ)) * Complex.I) = 0 := by
    rw [Complex.sin_mul_I, h0, zero_mul]
  obtain ⟨n, hn'⟩ := Complex.sin_eq_zero_iff.mp hs
  have hnorm : ‖(l * ((1 / (‖l‖ + 1) : ℝ) : ℂ)) * Complex.I‖ = ‖l‖ / (‖l‖ + 1) := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hx.le]
    field_simp
  rw [hn'] at hnorm
  have h1 : ‖l‖ / (‖l‖ + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h2 : ‖((n : ℂ) * (Real.pi : ℂ))‖ = |(n : ℝ)| * Real.pi := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2] at hnorm
  have hn0 : n = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
      have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
      simpa using this
    nlinarith [Real.pi_gt_three]
  have h3 : l * ((1 / (‖l‖ + 1) : ℝ) : ℂ) * Complex.I = 0 := by rw [hn', hn0]; simp
  have h4 : ((1 / (‖l‖ + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  exact (mul_ne_zero (mul_ne_zero hl h4) Complex.I_ne_zero) h3

theorem solution (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hε : 0 < ε)
    (ω : ℂ) (hω : ω ≠ -(a : ℂ)) :
    ω ∈ delaySpectrum a k ε ↔ h a k ε ω = 0 := by
  have hl : (a : ℂ) + ω ≠ 0 := fun h0 => hω (by linear_combination h0)
  have hexp : Complex.exp ((a : ℂ) + ω) / 2 ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) two_ne_zero
  have hkey := key_identity a k ε ω
  constructor
  · rintro ⟨φ, hφ, x₁, hx₁, hφx₁⟩
    have hexpl := eig_explicit a k ε ω φ hφ
    have hc : deriv φ 0 ≠ 0 := by
      intro hc0
      have := (hexpl x₁ hx₁).2
      rw [hc0, zero_mul] at this
      exact hφx₁ ((mul_eq_zero.mp this).resolve_left hl)
    obtain ⟨d1, e1⟩ := hexpl 1 ⟨zero_le_one, le_rfl⟩
    simp only [Complex.ofReal_one, mul_one] at d1 e1
    have hb := hφ.right
    have : deriv φ 0 * (Complex.exp ((a : ℂ) + ω) / 2 * h a k ε ω) = 0 := by
      rw [← hkey]
      linear_combination ((a : ℂ) + ω) * hb - ((a : ℂ) + ω) * d1
        - ((k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω)) * e1
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hc
    · exact (mul_eq_zero.mp h1).resolve_left hexp
  · intro hh
    set l : ℂ := (a : ℂ) + ω with hl'
    have hlin : ∀ x : ℝ, HasDerivAt (fun x : ℝ => l * (x : ℂ)) l x := by
      intro x
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul l
    have hsh : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.sinh (l * (x : ℂ)))
        (l * Complex.cosh (l * (x : ℂ))) x := fun x => by
      have := (Complex.hasDerivAt_sinh (l * (x : ℂ))).scomp x (hlin x)
      exact this.congr_deriv (by simp [smul_eq_mul])
    have hch : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.cosh (l * (x : ℂ)))
        (l * Complex.sinh (l * (x : ℂ))) x := fun x => by
      have := (Complex.hasDerivAt_cosh (l * (x : ℂ))).scomp x (hlin x)
      exact this.congr_deriv (by simp [smul_eq_mul])
    have hd1 : deriv (fun x : ℝ => Complex.sinh (l * (x : ℂ))) = fun x : ℝ => l * Complex.cosh (l * (x : ℂ)) :=
      funext fun x => (hsh x).deriv
    have hd2 : deriv (deriv (fun x : ℝ => Complex.sinh (l * (x : ℂ))))
        = fun x : ℝ => l * (l * Complex.sinh (l * (x : ℂ))) := by
      rw [hd1]; exact funext fun x => ((hch x).const_mul l).deriv
    refine ⟨fun x : ℝ => Complex.sinh (l * (x : ℂ)), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · -- ContDiff
      have h0 : ContDiff ℝ 2 (fun x : ℝ => l * (x : ℂ)) :=
        contDiff_const.mul Complex.ofRealCLM.contDiff
      exact (Complex.contDiff_sinh.restrict_scalars ℝ).comp h0
    · intro x _
      rw [hd2]; ring
    · simp
    · rw [hd1]
      have hh' : l * Complex.cosh l + (k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω) * Complex.sinh l = 0 := by
        rw [hkey, hh, mul_zero]
      simp only [Complex.ofReal_one, mul_one]
      linear_combination hh'
    · refine ⟨1 / (‖l‖ + 1), ⟨by positivity, ?_⟩, sinh_lx_ne_zero l hl⟩
      rw [div_le_one (by positivity)]
      linarith [norm_nonneg l]

end
