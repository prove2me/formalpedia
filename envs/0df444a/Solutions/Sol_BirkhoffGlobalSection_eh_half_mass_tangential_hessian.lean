-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_half_mass_tangential_hessian
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T19:56:51.173159+00:00
-- url     : https://prove2.me/submissions/3957fd16-1d78-48fc-af6f-91503947ec7a

import Definitions.Def_BirkhoffGlobalSection_EHConvexPerturbation
import Theorems.Thm_BirkhoffGlobalSection_eh_half_mass_corner_determinant_pos
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Equal-mass tangential Hessian. The derivatives are explicit (`fderiv_Ghalf`, `hess_Ghalf`):
`d²G[v,v] = |ζ|² + c_θ ξ₁² + d_θ ξ₂²` with the constraint `P·ζ + ∇V·ξ = 0`.
Cauchy--Schwarz reduces positivity to `c_θ > 0` and `D = r² c_θ d_θ + c_θ V₂² + d_θ V₁² > 0`
(`quad_pos_of_det`). `D` is bilinear in `(c_θ, d_θ)`, which range over the box
`V₁₁ ± r|sinh 2x₁|/2`, `V₂₂ ± r|sin 2x₂|/2`, so its four corner values suffice (`bilinear_pos`).
`c_θ > 0` is proved here (`cmin_pos`: monotone in `c`, worst at `x₂ = 0`, then a polynomial
inequality). The corner values are the imported leaf. -/

namespace BirkhoffGlobalSection

namespace EHConvex

open Set

noncomputable section

/-- Equal-mass EH potential. -/
def Vh (c x₁ x₂ : ℝ) : ℝ :=
  c * (Real.cosh x₁ ^ 2 - Real.cos x₂ ^ 2) / 4 - Real.cosh x₁ / 2 -
    Real.sinh (2 * x₁) ^ 2 / 128 - Real.sin (2 * x₂) ^ 2 / 128

/-- `x · ∇V`. -/
def Wh (c x₁ x₂ : ℝ) : ℝ :=
  x₁ * (c * Real.cosh x₁ * Real.sinh x₁ / 2 - Real.sinh x₁ / 2 -
      Real.sinh (2 * x₁) * Real.cosh (2 * x₁) / 32) +
    x₂ * (c * Real.cos x₂ * Real.sin x₂ / 2 - Real.sin (2 * x₂) * Real.cos (2 * x₂) / 32)

/-- `x · ∇F - F` for the magnetic term `F = (sin 2x₂, sinh 2x₁)/8`. -/
def g1 (x₂ : ℝ) : ℝ := x₂ * Real.cos (2 * x₂) / 4 - Real.sin (2 * x₂) / 8

def g2 (x₁ : ℝ) : ℝ := x₁ * Real.cosh (2 * x₁) / 4 - Real.sinh (2 * x₁) / 8

theorem G_half_eq (c : ℝ) (s : Phase) :
    ehLeftHamiltonian (1 / 2) c s =
      ((s 2 + Real.sin (2 * s 1) / 8) ^ 2 + (s 3 + Real.sinh (2 * s 0) / 8) ^ 2) / 2 +
        Vh c (s 0) (s 1) := by
  unfold ehLeftHamiltonian Vh
  simp only
  ring

/-- The radial derivative at equal masses. -/
theorem radial_derivative_half (c : ℝ) (s : Phase) :
    fderiv ℝ (ehLeftHamiltonian (1 / 2) c) s s =
      (s 2 + Real.sin (2 * s 1) / 8) ^ 2 + (s 3 + Real.sinh (2 * s 0) / 8) ^ 2 +
        (s 2 + Real.sin (2 * s 1) / 8) * g1 (s 1) +
        (s 3 + Real.sinh (2 * s 0) / 8) * g2 (s 0) + Wh c (s 0) (s 1) := by
  have hG : ContDiff ℝ 1 (ehLeftHamiltonian (1 / 2) c) := by
    unfold ehLeftHamiltonian; fun_prop
  have h1 := ray_hasDerivAt hG s 1
  rw [one_smul] at h1
  have h2 : HasDerivAt (fun t : ℝ => ehLeftHamiltonian (1 / 2) c (t • s))
      ((s 2 + Real.sin (2 * s 1) / 8) ^ 2 + (s 3 + Real.sinh (2 * s 0) / 8) ^ 2 +
        (s 2 + Real.sin (2 * s 1) / 8) * g1 (s 1) +
        (s 3 + Real.sinh (2 * s 0) / 8) * g2 (s 0) + Wh c (s 0) (s 1)) 1 := by
    have e : (fun t : ℝ => ehLeftHamiltonian (1 / 2) c (t • s)) = fun t =>
        ((t * s 2 + Real.sin (2 * (t * s 1)) / 8) ^ 2 +
          (t * s 3 + Real.sinh (2 * (t * s 0)) / 8) ^ 2) / 2 +
        (c * (Real.cosh (t * s 0) ^ 2 - Real.cos (t * s 1) ^ 2) / 4 - Real.cosh (t * s 0) / 2 -
          Real.sinh (2 * (t * s 0)) ^ 2 / 128 - Real.sin (2 * (t * s 1)) ^ 2 / 128) := by
      funext t
      rw [G_half_eq]
      simp [Vh, Pi.smul_apply, smul_eq_mul]
    rw [e]
    have hl : ∀ k : ℝ, HasDerivAt (fun t : ℝ => t * k) k 1 := fun k => by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const k
    have hl2 : ∀ k : ℝ, HasDerivAt (fun t : ℝ => 2 * (t * k)) (2 * k) 1 := fun k =>
      (hl k).const_mul 2
    have dsin2 := fun k => (hl2 k).sin
    have dsinh2 := fun k => (hl2 k).sinh
    have dcosh := fun k => (hl k).cosh
    have dcos := fun k => (hl k).cos
    have := ((((hl (s 2)).add ((dsin2 (s 1)).div_const 8)).pow 2).add
        (((hl (s 3)).add ((dsinh2 (s 0)).div_const 8)).pow 2)).div_const 2 |>.add
      (((((((dcosh (s 0)).pow 2).sub ((dcos (s 1)).pow 2)).const_mul c).div_const 4).sub
        ((dcosh (s 0)).div_const 2)).sub (((dsinh2 (s 0)).pow 2).div_const 128) |>.sub
        (((dsin2 (s 1)).pow 2).div_const 128))
    refine this.congr_deriv ?_
    simp only [one_mul, g1, g2, Wh, Pi.add_apply, Pi.pow_apply]
    norm_num
    ring
  exact h1.unique h2

/-- The parameter-free radial estimate at the critical energy `c = 2`. -/
def CriticalRadialEstimate : Prop :=
  ∀ x₁ x₂ u₁ u₂ : ℝ, |x₂| ≤ Real.pi / 2 → Real.cosh x₁ ≤ 2 →
    u₁ ^ 2 + u₂ ^ 2 ≤ -2 * Vh 2 x₁ x₂ →
    0 ≤ u₁ ^ 2 + u₂ ^ 2 + u₁ * g1 x₂ + u₂ * g2 x₁ + Wh 2 x₁ x₂

theorem Vh_eq (c x₁ x₂ : ℝ) :
    Vh c x₁ x₂ = Vh 2 x₁ x₂ + (c - 2) * (Real.cosh x₁ ^ 2 - Real.cos x₂ ^ 2) / 4 := by
  unfold Vh; ring

theorem Wh_eq (c x₁ x₂ : ℝ) :
    Wh c x₁ x₂ = Wh 2 x₁ x₂ + (c - 2) *
      (x₁ * Real.sinh x₁ * Real.cosh x₁ + x₂ * Real.sin x₂ * Real.cos x₂) / 2 := by
  unfold Wh; ring

theorem cos_sq_le_cosh_sq (x₁ x₂ : ℝ) : Real.cos x₂ ^ 2 ≤ Real.cosh x₁ ^ 2 := by
  have h1 : Real.cos x₂ ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact Real.abs_cos_le_one _
  have h2 := Real.one_le_cosh x₁
  nlinarith

theorem mul_sinh_nonneg (x : ℝ) : 0 ≤ x * Real.sinh x := by
  rcases le_total 0 x with h | h
  · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr h)
  · exact mul_nonneg_of_nonpos_of_nonpos h (Real.sinh_nonpos_iff.mpr h)

theorem mul_sinh_pos {x : ℝ} (hx : x ≠ 0) : 0 < x * Real.sinh x := by
  rcases lt_or_gt_of_ne hx with h | h
  · exact mul_pos_of_neg_of_neg h (Real.sinh_neg_iff.mpr h)
  · exact mul_pos h (Real.sinh_pos_iff.mpr h)

theorem mul_sin_nonneg {x : ℝ} (hx : |x| ≤ Real.pi / 2) : 0 ≤ x * Real.sin x := by
  have hpi := Real.pi_pos
  rcases le_total 0 x with h | h
  · exact mul_nonneg h (Real.sin_nonneg_of_nonneg_of_le_pi h (by
      have := le_abs_self x; linarith))
  · apply mul_nonneg_of_nonpos_of_nonpos h
    have := Real.sin_nonneg_of_nonneg_of_le_pi (x := -x) (by linarith) (by
      have := neg_abs_le x; linarith)
    rw [Real.sin_neg] at this; linarith

theorem mul_sin_pos {x : ℝ} (hx : |x| ≤ Real.pi / 2) (h0 : x ≠ 0) : 0 < x * Real.sin x := by
  have hpi := Real.pi_pos
  rcases lt_or_gt_of_ne h0 with h | h
  · apply mul_pos_of_neg_of_neg h
    have := Real.sin_pos_of_pos_of_lt_pi (x := -x) (by linarith) (by
      have := neg_abs_le x; linarith)
    rw [Real.sin_neg] at this; linarith
  · exact mul_pos h (Real.sin_pos_of_pos_of_lt_pi h (by have := le_abs_self x; linarith))

theorem cos_nonneg_of_abs_le {x : ℝ} (hx : |x| ≤ Real.pi / 2) : 0 ≤ Real.cos x :=
  Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by have := neg_abs_le x; linarith)
    (by have := le_abs_self x; linarith)

/-- On the zero level inside the box, `cosh x₁ ≤ 2`. -/
theorem cosh_le_two {c x₁ x₂ : ℝ} (hc : 2 < c) (h0 : Real.cosh x₁ ^ 2 ≤ 2 * c)
    (hV : Vh c x₁ x₂ ≤ 0) : Real.cosh x₁ ≤ 2 := by
  by_contra ha
  push_neg at ha
  unfold Vh at hV
  rw [sinh_two_sq, sin_two_sq] at hV
  set a := Real.cosh x₁
  set b := Real.cos x₂
  have hb1 : b ^ 2 ≤ 1 := by rw [sq_le_one_iff_abs_le_one]; exact Real.abs_cos_le_one _
  have hb0 : 0 ≤ b ^ 2 := sq_nonneg _
  have hbt : c * b ^ 2 / 4 + b ^ 2 * (1 - b ^ 2) / 32 ≤ c / 4 := by
    nlinarith [mul_nonneg hb0 (by linarith : (0:ℝ) ≤ 1 - b ^ 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - b ^ 2) (by linarith : (0:ℝ) ≤ c - 1 / 8)]
  have hq : a ^ 2 * (a ^ 2 - 1) ≤ 2 * c * (a ^ 2 - 1) :=
    mul_le_mul_of_nonneg_right h0 (by nlinarith)
  nlinarith [mul_pos (by linarith : (0:ℝ) < a - 2) (by linarith : (0:ℝ) < a),
    mul_pos (mul_pos (by linarith : (0:ℝ) < a - 2) (by linarith : (0:ℝ) < a))
      (by linarith : (0:ℝ) < a)]

/-- Reduction of the equal-mass star-shapedness estimate to `c = 2`. -/
theorem star_of_critical (hcrit : CriticalRadialEstimate) (c : ℝ) (hc : 2 < c) (s : Phase)
    (hs : ehLeftHamiltonian (1 / 2) c s = 0)
    (h1 : |s 1| ≤ Real.pi / 2) (h0 : Real.cosh (s 0) ^ 2 ≤ 2 * c) :
    0 < fderiv ℝ (ehLeftHamiltonian (1 / 2) c) s s := by
  rw [radial_derivative_half]
  rw [G_half_eq] at hs
  set P₁ := s 2 + Real.sin (2 * s 1) / 8
  set P₂ := s 3 + Real.sinh (2 * s 0) / 8
  have hP : P₁ ^ 2 + P₂ ^ 2 = -2 * Vh c (s 0) (s 1) := by linarith
  have hVc : Vh c (s 0) (s 1) ≤ 0 := by nlinarith [sq_nonneg P₁, sq_nonneg P₂]
  have hD := cos_sq_le_cosh_sq (s 0) (s 1)
  have hP2 : P₁ ^ 2 + P₂ ^ 2 ≤ -2 * Vh 2 (s 0) (s 1) := by
    rw [hP, Vh_eq c]; nlinarith
  have hcrit' := hcrit (s 0) (s 1) P₁ P₂ h1 (cosh_le_two hc h0 hVc) hP2
  rw [Wh_eq c]
  have hT1 : 0 ≤ s 0 * Real.sinh (s 0) * Real.cosh (s 0) :=
    mul_nonneg (mul_sinh_nonneg _) (Real.cosh_pos _).le
  have hT2 : 0 ≤ s 1 * Real.sin (s 1) * Real.cos (s 1) :=
    mul_nonneg (mul_sin_nonneg h1) (cos_nonneg_of_abs_le h1)
  have key : 0 < (c - 2) * (s 0 * Real.sinh (s 0) * Real.cosh (s 0) +
      s 1 * Real.sin (s 1) * Real.cos (s 1)) / 2 ∨
      (s 0 = 0 ∧ s 1 = 0) := by
    by_cases hx0 : s 0 = 0
    · by_cases hx1 : s 1 = 0
      · exact Or.inr ⟨hx0, hx1⟩
      · left
        have hcos : 0 < Real.cos (s 1) := by
          rcases (cos_nonneg_of_abs_le h1).lt_or_eq with h | h
          · exact h
          · exfalso
            have hb : Real.cos (s 1) = 0 := h.symm
            have : Vh c (s 0) (s 1) = c / 4 - 1 / 2 := by
              unfold Vh
              rw [hx0, Real.sin_two_mul, hb]
              simp
            linarith
        have := mul_pos (mul_sin_pos h1 hx1) hcos
        have : 0 < c - 2 := by linarith
        positivity
    · left
      have := mul_pos (mul_sinh_pos hx0) (Real.cosh_pos (s 0))
      have : 0 < c - 2 := by linarith
      positivity
  rcases key with hk | ⟨hx0, hx1⟩
  · linarith
  · have hV0 : Vh c (s 0) (s 1) = -1 / 2 := by
      unfold Vh; rw [hx0, hx1]; simp; ring
    have hg : g1 (s 1) = 0 ∧ g2 (s 0) = 0 := by
      unfold g1 g2; rw [hx0, hx1]; simp
    have hW : Wh 2 (s 0) (s 1) = 0 := by unfold Wh; rw [hx0, hx1]; simp
    rw [hg.1, hg.2, hW, hx0, hx1]
    simp only [mul_zero, zero_mul, Real.sinh_zero, Real.sin_zero, add_zero]
    nlinarith

/-- A function vanishing at `0` with nonnegative derivative on `[0, ∞)` is
nonnegative there. -/
theorem nonneg_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (hf y).continuousAt.continuousWithinAt
    · exact fun y _ => (hf y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hf y).deriv]; exact hd y (le_of_lt hy)
  have := hmono (Set.mem_Ici.mpr le_rfl) hx hx
  rwa [h0] at this

theorem hasDerivAt_g2 (x : ℝ) : HasDerivAt g2 (x * Real.sinh (2 * x) / 2) x := by
  have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have := (((hasDerivAt_id x).mul h2.cosh).div_const 4).sub (h2.sinh.div_const 8)
  refine this.congr_deriv ?_ |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · simp; ring
  · simp [g2]

theorem hasDerivAt_g1 (y : ℝ) : HasDerivAt g1 (-(y * Real.sin (2 * y)) / 2) y := by
  have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 y := by
    simpa using (hasDerivAt_id y).const_mul (2 : ℝ)
  have := (((hasDerivAt_id y).mul h2.cos).div_const 4).sub (h2.sin.div_const 8)
  refine this.congr_deriv ?_ |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  · simp; ring
  · simp [g1]

theorem g2_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ g2 x :=
  nonneg_of_hasDerivAt hasDerivAt_g2 (by simp [g2])
    (fun y hy => by
      have := mul_nonneg hy (Real.sinh_nonneg_iff.mpr (by linarith : 0 ≤ 2 * y)); linarith) hx

theorem g2_le {x : ℝ} (hx : 0 ≤ x) : g2 x ≤ x * Real.sinh x ^ 2 / 2 := by
  have h : ∀ y, HasDerivAt (fun y => y * Real.sinh y ^ 2 / 2 - g2 y) (Real.sinh y ^ 2 / 2) y := by
    intro y
    have := (((hasDerivAt_id y).mul ((Real.hasDerivAt_sinh y).pow 2)).div_const 2).sub
      (hasDerivAt_g2 y)
    refine this.congr_deriv ?_
    simp [Real.sinh_two_mul]; ring
  have := nonneg_of_hasDerivAt h (by simp [g2]) (fun y _ => by positivity) hx
  linarith

theorem g1_nonpos {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ Real.pi / 2) : g1 y ≤ 0 := by
  have hanti : AntitoneOn g1 (Icc 0 (Real.pi / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun z _ => (hasDerivAt_g1 z).continuousAt.continuousWithinAt
    · exact fun z _ => (hasDerivAt_g1 z).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hasDerivAt_g1 z).deriv]
      have : 0 ≤ Real.sin (2 * z) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hz.1]) (by linarith [hz.2])
      have := mul_nonneg hz.1.le this
      linarith
  have := hanti ⟨le_rfl, by positivity⟩ ⟨hy, hy'⟩ hy
  simpa [g1] using this

theorem neg_g1_le {y : ℝ} (hy : 0 ≤ y) : -g1 y ≤ y * Real.sin y ^ 2 / 2 := by
  have h : ∀ z, HasDerivAt (fun z => z * Real.sin z ^ 2 / 2 + g1 z) (Real.sin z ^ 2 / 2) z := by
    intro z
    have := (((hasDerivAt_id z).mul ((Real.hasDerivAt_sin z).pow 2)).div_const 2).add
      (hasDerivAt_g1 z)
    refine this.congr_deriv ?_
    simp [Real.sin_two_mul]; ring
  have := nonneg_of_hasDerivAt h (by simp [g1]) (fun z _ => by positivity) hy
  linarith

theorem g2_neg (x : ℝ) : g2 (-x) = -g2 x := by
  unfold g2; rw [mul_neg, Real.cosh_neg, Real.sinh_neg]; ring

theorem g1_neg (y : ℝ) : g1 (-y) = -g1 y := by
  unfold g1; rw [mul_neg, Real.cos_neg, Real.sin_neg]; ring

theorem g2_sq_le (x : ℝ) : g2 x ^ 2 ≤ (x * Real.sinh x) ^ 2 * Real.sinh x ^ 2 / 4 := by
  have key : ∀ x : ℝ, 0 ≤ x → g2 x ^ 2 ≤ (x * Real.sinh x) ^ 2 * Real.sinh x ^ 2 / 4 := by
    intro x hx
    have h0 := g2_nonneg hx
    have h1 := g2_le hx
    have : g2 x ^ 2 ≤ (x * Real.sinh x ^ 2 / 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
    calc g2 x ^ 2 ≤ (x * Real.sinh x ^ 2 / 2) ^ 2 := this
      _ = (x * Real.sinh x) ^ 2 * Real.sinh x ^ 2 / 4 := by ring
  rcases le_total 0 x with hx | hx
  · exact key x hx
  · have := key (-x) (by linarith)
    rw [g2_neg, Real.sinh_neg] at this
    calc g2 x ^ 2 = (-g2 x) ^ 2 := by ring
      _ ≤ _ := this
      _ = _ := by ring

theorem g1_sq_le {y : ℝ} (hy : |y| ≤ Real.pi / 2) :
    g1 y ^ 2 ≤ (y * Real.sin y) ^ 2 * Real.sin y ^ 2 / 4 := by
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ Real.pi / 2 →
      g1 y ^ 2 ≤ (y * Real.sin y) ^ 2 * Real.sin y ^ 2 / 4 := by
    intro y hy hy'
    have h0 := g1_nonpos hy hy'
    have h1 := neg_g1_le hy
    have : (-g1 y) ^ 2 ≤ (y * Real.sin y ^ 2 / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    calc g1 y ^ 2 = (-g1 y) ^ 2 := by ring
      _ ≤ (y * Real.sin y ^ 2 / 2) ^ 2 := this
      _ = (y * Real.sin y) ^ 2 * Real.sin y ^ 2 / 4 := by ring
  rcases le_total 0 y with h | h
  · exact key y h (by have := le_abs_self y; linarith)
  · have := key (-y) (by linarith) (by have := neg_abs_le y; linarith)
    rw [g1_neg, Real.sin_neg] at this
    calc g1 y ^ 2 = (-g1 y) ^ 2 := by ring
      _ ≤ _ := this
      _ = _ := by ring

theorem poly_V2_lo {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    -(1 / 2) ≤ -(b ^ 2) / 2 - b ^ 2 * (1 - b ^ 2) / 32 := by
  have h1 : 0 ≤ 1 - b ^ 2 := by nlinarith
  have h2 : 0 ≤ 16 - b ^ 2 := by nlinarith
  nlinarith [mul_nonneg h1 h2]

theorem poly_V1_nonneg {a : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    0 ≤ a ^ 2 / 2 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32 := by
  have h : 0 ≤ 16 - a * (a + 1) := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ a - 1) (by linarith : (0:ℝ) ≤ a)) h]

theorem poly_p_nonneg {a : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    0 ≤ a - 1 / 2 - a * (2 * a ^ 2 - 1) / 16 := by nlinarith

theorem poly_q_nonneg {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ b * (17 - 2 * b ^ 2) / 16 :=
  div_nonneg (mul_nonneg hb0 (by nlinarith)) (by norm_num)

theorem poly_E1 {a : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    (1 - 2 * (a ^ 2 / 2 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32)) * (a ^ 2 - 1) / 4 ≤
      (a - 1 / 2 - a * (2 * a ^ 2 - 1) / 16) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ha2),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ha2)) (sub_nonneg.mpr ha1),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ha2)) (sub_nonneg.mpr ha2)]

theorem poly_E2 (b : ℝ) :
    (-2 * (-(b ^ 2) / 2 - b ^ 2 * (1 - b ^ 2) / 32)) * (1 - b ^ 2) / 4 ≤
      (b * (17 - 2 * b ^ 2) / 16) ^ 2 := by
  nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg b) (sq_nonneg b)]

/-- The algebraic core of the critical estimate. -/
theorem critical_core {A B p q V₁ V₂ u₁ u₂ G₁ G₂ a b : ℝ}
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hR : u₁ ^ 2 + u₂ ^ 2 ≤ -2 * (V₁ + V₂)) (hV₁ : 0 ≤ V₁) (hV₂ : -(1 / 2) ≤ V₂)
    (hE1 : (1 - 2 * V₁) * (a ^ 2 - 1) / 4 ≤ p ^ 2) (hE2 : (-2 * V₂) * (1 - b ^ 2) / 4 ≤ q ^ 2)
    (hg2 : G₂ ^ 2 ≤ A ^ 2 * (a ^ 2 - 1) / 4) (hg1 : G₁ ^ 2 ≤ B ^ 2 * (1 - b ^ 2) / 4) :
    0 ≤ u₁ ^ 2 + u₂ ^ 2 + u₁ * G₁ + u₂ * G₂ + (A * p + B * q) := by
  have hc2 : (u₂ * G₂) ^ 2 ≤ (A * p) ^ 2 := by
    have e1 : u₂ ^ 2 ≤ 1 - 2 * V₁ := by nlinarith [sq_nonneg u₁]
    calc (u₂ * G₂) ^ 2 = u₂ ^ 2 * G₂ ^ 2 := by ring
      _ ≤ (1 - 2 * V₁) * (A ^ 2 * (a ^ 2 - 1) / 4) :=
          mul_le_mul e1 hg2 (sq_nonneg _) (by nlinarith [sq_nonneg u₂])
      _ = A ^ 2 * ((1 - 2 * V₁) * (a ^ 2 - 1) / 4) := by ring
      _ ≤ A ^ 2 * p ^ 2 := mul_le_mul_of_nonneg_left hE1 (sq_nonneg A)
      _ = (A * p) ^ 2 := by ring
  have hc1 : (u₁ * G₁) ^ 2 ≤ (B * q) ^ 2 := by
    have e1 : u₁ ^ 2 ≤ -2 * V₂ := by nlinarith [sq_nonneg u₂]
    calc (u₁ * G₁) ^ 2 = u₁ ^ 2 * G₁ ^ 2 := by ring
      _ ≤ (-2 * V₂) * (B ^ 2 * (1 - b ^ 2) / 4) :=
          mul_le_mul e1 hg1 (sq_nonneg _) (by nlinarith [sq_nonneg u₁])
      _ = B ^ 2 * ((-2 * V₂) * (1 - b ^ 2) / 4) := by ring
      _ ≤ B ^ 2 * q ^ 2 := mul_le_mul_of_nonneg_left hE2 (sq_nonneg B)
      _ = (B * q) ^ 2 := by ring
  have hW1 : 0 ≤ A * p := mul_nonneg hA0 hp0
  have hW2 : 0 ≤ B * q := mul_nonneg hB0 hq0
  have k2 := (abs_le_of_sq_le_sq' hc2 hW1).1
  have k1 := (abs_le_of_sq_le_sq' hc1 hW2).1
  nlinarith [sq_nonneg u₁, sq_nonneg u₂]

theorem critical_radial_estimate : CriticalRadialEstimate := by
  intro x₁ x₂ u₁ u₂ h2 h1 hu
  have hpy : Real.sinh x₁ ^ 2 = Real.cosh x₁ ^ 2 - 1 := by rw [Real.cosh_sq]; ring
  have htr : Real.sin x₂ ^ 2 = 1 - Real.cos x₂ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq x₂]
  have ha1 : 1 ≤ Real.cosh x₁ := Real.one_le_cosh x₁
  have hb0 : 0 ≤ Real.cos x₂ := cos_nonneg_of_abs_le h2
  have hb1 : Real.cos x₂ ≤ 1 := Real.cos_le_one x₂
  have hW : Wh 2 x₁ x₂ =
      x₁ * Real.sinh x₁ * (Real.cosh x₁ - 1 / 2 - Real.cosh x₁ * (2 * Real.cosh x₁ ^ 2 - 1) / 16) +
      x₂ * Real.sin x₂ * (Real.cos x₂ * (17 - 2 * Real.cos x₂ ^ 2) / 16) := by
    unfold Wh
    rw [Real.sinh_two_mul, Real.cosh_two_mul, Real.sin_two_mul, Real.cos_two_mul]
    linear_combination (-(x₁ * Real.sinh x₁ * Real.cosh x₁) / 16) * hpy
  have hV : Vh 2 x₁ x₂ =
      (Real.cosh x₁ ^ 2 / 2 - Real.cosh x₁ / 2 - Real.cosh x₁ ^ 2 * (Real.cosh x₁ ^ 2 - 1) / 32) +
      (-(Real.cos x₂ ^ 2) / 2 - Real.cos x₂ ^ 2 * (1 - Real.cos x₂ ^ 2) / 32) := by
    unfold Vh
    rw [sinh_two_sq, sin_two_sq]
    ring
  have hg2 := g2_sq_le x₁
  rw [hpy] at hg2
  have hg1 := g1_sq_le h2
  rw [htr] at hg1
  rw [hW]
  rw [hV] at hu
  exact critical_core (poly_p_nonneg ha1 h1) (poly_q_nonneg hb0 hb1) (mul_sinh_nonneg x₁)
    (mul_sin_nonneg h2) hu (poly_V1_nonneg ha1 h1) (poly_V2_lo hb0 hb1) (poly_E1 ha1 h1)
    (poly_E2 _) hg2 hg1

/-- `∂V/∂x₁` and `∂V/∂x₂`. -/
def V1 (c x₁ : ℝ) : ℝ :=
  c * Real.cosh x₁ * Real.sinh x₁ / 2 - Real.sinh x₁ / 2 -
    Real.sinh (2 * x₁) * Real.cosh (2 * x₁) / 32

def V2 (c x₂ : ℝ) : ℝ :=
  c * Real.cos x₂ * Real.sin x₂ / 2 - Real.sin (2 * x₂) * Real.cos (2 * x₂) / 32

/-- `∂²V/∂x₁²` and `∂²V/∂x₂²` (the potential is decoupled). -/
def V11 (c x₁ : ℝ) : ℝ := c * Real.cosh (2 * x₁) / 2 - Real.cosh x₁ / 2 - Real.cosh (4 * x₁) / 16

def V22 (c x₂ : ℝ) : ℝ := c * Real.cos (2 * x₂) / 2 - Real.cos (4 * x₂) / 16

/-- First derivative of the equal-mass Hamiltonian, in closed form. -/
def E1 (c : ℝ) (s v : Phase) : ℝ :=
  (s 2 + Real.sin (2 * s 1) / 8) * (v 2 + Real.cos (2 * s 1) / 4 * v 1) +
    (s 3 + Real.sinh (2 * s 0) / 8) * (v 3 + Real.cosh (2 * s 0) / 4 * v 0) +
    V1 c (s 0) * v 0 + V2 c (s 1) * v 1

/-- Second derivative along `v`, in closed form. -/
def E2 (c : ℝ) (s v : Phase) : ℝ :=
  (v 2 + Real.cos (2 * s 1) / 4 * v 1) ^ 2 + (v 3 + Real.cosh (2 * s 0) / 4 * v 0) ^ 2 +
    ((s 3 + Real.sinh (2 * s 0) / 8) * (Real.sinh (2 * s 0) / 2) + V11 c (s 0)) * v 0 ^ 2 +
    (-(s 2 + Real.sin (2 * s 1) / 8) * (Real.sin (2 * s 1) / 2) + V22 c (s 1)) * v 1 ^ 2

theorem contDiff_Ghalf (c : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (ehLeftHamiltonian (1 / 2) c) := by
  unfold ehLeftHamiltonian; fun_prop

theorem fderiv_Ghalf (c : ℝ) (s v : Phase) :
    fderiv ℝ (ehLeftHamiltonian (1 / 2) c) s v = E1 c s v := by
  have hd : DifferentiableAt ℝ (ehLeftHamiltonian (1 / 2) c) s :=
    (contDiff_Ghalf c (n := 1)).differentiable one_ne_zero s
  rw [← hd.lineDeriv_eq_fderiv]
  unfold lineDeriv
  have e : (fun t : ℝ => ehLeftHamiltonian (1 / 2) c (s + t • v)) = fun t =>
      ((s 2 + t * v 2 + Real.sin (2 * (s 1 + t * v 1)) / 8) ^ 2 +
        (s 3 + t * v 3 + Real.sinh (2 * (s 0 + t * v 0)) / 8) ^ 2) / 2 +
      Vh c (s 0 + t * v 0) (s 1 + t * v 1) := by
    funext t; rw [G_half_eq]; simp
  rw [e]
  have hl : ∀ a k : ℝ, HasDerivAt (fun t : ℝ => a + t * k) k 0 := fun a k => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add a
  have h2 : ∀ a k : ℝ, HasDerivAt (fun t : ℝ => 2 * (a + t * k)) (2 * k) 0 := fun a k =>
    (hl a k).const_mul 2
  have hP1 := ((hl (s 2) (v 2)).add ((h2 (s 1) (v 1)).sin.div_const 8))
  have hP2 := ((hl (s 3) (v 3)).add ((h2 (s 0) (v 0)).sinh.div_const 8))
  have hx0 := hl (s 0) (v 0)
  have hx1 := hl (s 1) (v 1)
  have hV : HasDerivAt (fun t : ℝ => Vh c (s 0 + t * v 0) (s 1 + t * v 1))
      (V1 c (s 0) * v 0 + V2 c (s 1) * v 1) 0 := by
    unfold Vh
    have := (((((hx0.cosh.pow 2).sub (hx1.cos.pow 2)).const_mul c).div_const 4).sub
      (hx0.cosh.div_const 2)).sub ((h2 (s 0) (v 0)).sinh.pow 2 |>.div_const 128) |>.sub
      ((h2 (s 1) (v 1)).sin.pow 2 |>.div_const 128)
    refine this.congr_deriv ?_
    simp [V1, V2]
    rw [Real.sinh_two_mul, Real.cosh_two_mul, Real.sin_two_mul, Real.cos_two_mul]
    ring
  have h := (((hP1.pow 2).add (hP2.pow 2)).div_const 2).add hV
  have h' : HasDerivAt (fun t : ℝ => ((s 2 + t * v 2 + Real.sin (2 * (s 1 + t * v 1)) / 8) ^ 2 +
      (s 3 + t * v 3 + Real.sinh (2 * (s 0 + t * v 0)) / 8) ^ 2) / 2 +
      Vh c (s 0 + t * v 0) (s 1 + t * v 1)) _ 0 := h
  rw [h'.deriv]
  simp [E1]
  ring

theorem hasDerivAt_V1 (c x : ℝ) : HasDerivAt (V1 c) (V11 c x) x := by
  unfold V1
  have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have := ((((Real.hasDerivAt_cosh x).const_mul c).mul (Real.hasDerivAt_sinh x)).div_const 2 |>.sub
    ((Real.hasDerivAt_sinh x).div_const 2)).sub ((h2.sinh.mul h2.cosh).div_const 32)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · simp only [V11]
    rw [show (4 : ℝ) * x = 2 * (2 * x) by ring, Real.cosh_two_mul (2 * x), Real.cosh_two_mul x]
    ring
  · simp

theorem hasDerivAt_V2 (c x : ℝ) : HasDerivAt (V2 c) (V22 c x) x := by
  unfold V2
  have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have := ((((Real.hasDerivAt_cos x).const_mul c).mul (Real.hasDerivAt_sin x)).div_const 2).sub
    ((h2.sin.mul h2.cos).div_const 32)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · simp only [V22]
    have h4 : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
      rw [show (4 : ℝ) * x = 2 * (2 * x) by ring, Real.cos_two_mul]
    linear_combination (-c / 2) * Real.cos_two_mul x + (-c / 2) * Real.sin_sq_add_cos_sq x +
      (1 / 16) * h4 + (1 / 16) * Real.sin_sq_add_cos_sq (2 * x)
  · simp

theorem hess_Ghalf (c : ℝ) (s v : Phase) :
    fderiv ℝ (fun x => fderiv ℝ (ehLeftHamiltonian (1 / 2) c) x v) s v = E2 c s v := by
  have e : (fun x => fderiv ℝ (ehLeftHamiltonian (1 / 2) c) x v) = fun x => E1 c x v := by
    funext x; exact fderiv_Ghalf c x v
  rw [e]
  have hd : DifferentiableAt ℝ (fun x => E1 c x v) s := by
    unfold E1 V1 V2; fun_prop
  rw [← hd.lineDeriv_eq_fderiv]
  unfold lineDeriv
  have hl : ∀ a k : ℝ, HasDerivAt (fun t : ℝ => a + t * k) k 0 := fun a k => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add a
  have h2 : ∀ a k : ℝ, HasDerivAt (fun t : ℝ => 2 * (a + t * k)) (2 * k) 0 := fun a k =>
    (hl a k).const_mul 2
  have hP1 := ((hl (s 2) (v 2)).add ((h2 (s 1) (v 1)).sin.div_const 8))
  have hP2 := ((hl (s 3) (v 3)).add ((h2 (s 0) (v 0)).sinh.div_const 8))
  have hZ1 := (((h2 (s 1) (v 1)).cos.div_const 4).mul_const (v 1)).const_add (v 2)
  have hZ2 := (((h2 (s 0) (v 0)).cosh.div_const 4).mul_const (v 0)).const_add (v 3)
  have hW1 := ((hasDerivAt_V1 c (s 0 + 0 * v 0)).comp (0 : ℝ) (hl (s 0) (v 0))).mul_const (v 0)
  have hW2 := ((hasDerivAt_V2 c (s 1 + 0 * v 1)).comp (0 : ℝ) (hl (s 1) (v 1))).mul_const (v 1)
  have h := ((hP1.mul hZ1).add (hP2.mul hZ2)).add hW1 |>.add hW2
  have h' : HasDerivAt (fun t : ℝ => E1 c (s + t • v) v) _ 0 :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by simp [E1, Function.comp])
  rw [h'.deriv]
  simp [E2]
  ring

/-- Algebraic criterion: positivity of `|ζ|² + c ξ₁² + d ξ₂²` under the tangency constraint. -/
theorem quad_pos_of_det {P₁ P₂ A B c d ξ₁ ξ₂ ζ₁ ζ₂ : ℝ} (hc : 0 < c)
    (hD : 0 < (P₁ ^ 2 + P₂ ^ 2) * c * d + c * B ^ 2 + d * A ^ 2)
    (htan : P₁ * ζ₁ + P₂ * ζ₂ + A * ξ₁ + B * ξ₂ = 0)
    (hne : ξ₁ ≠ 0 ∨ ξ₂ ≠ 0 ∨ ζ₁ ≠ 0 ∨ ζ₂ ≠ 0) :
    0 < ζ₁ ^ 2 + ζ₂ ^ 2 + c * ξ₁ ^ 2 + d * ξ₂ ^ 2 := by
  set R := P₁ ^ 2 + P₂ ^ 2 with hR
  by_cases hξ : ξ₁ = 0 ∧ ξ₂ = 0
  · obtain ⟨h1, h2⟩ := hξ
    subst h1; subst h2
    have : ζ₁ ≠ 0 ∨ ζ₂ ≠ 0 := by tauto
    rcases this with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg ζ₂]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg ζ₁]
  have hξpos : 0 < ξ₁ ^ 2 + ξ₂ ^ 2 := by
    rcases not_and_or.mp hξ with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg ξ₂]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg ξ₁]
  rcases eq_or_lt_of_le (show 0 ≤ R by positivity) with hR0 | hRpos
  · -- `P = 0`: the constraint is `A ξ₁ + B ξ₂ = 0`
    have hP1 : P₁ = 0 := by nlinarith [sq_nonneg P₁, sq_nonneg P₂]
    have hP2 : P₂ = 0 := by nlinarith [sq_nonneg P₁, sq_nonneg P₂]
    rw [hP1, hP2] at htan
    have hlin : A * ξ₁ + B * ξ₂ = 0 := by linarith
    rw [← hR0] at hD
    have hid : (c * ξ₁ ^ 2 + d * ξ₂ ^ 2) * (A ^ 2 + B ^ 2) =
        (c * B ^ 2 + d * A ^ 2) * (ξ₁ ^ 2 + ξ₂ ^ 2) +
          (c - d) * (A * ξ₁ - B * ξ₂) * (A * ξ₁ + B * ξ₂) := by ring
    rw [hlin, mul_zero, add_zero] at hid
    have hD' : 0 < c * B ^ 2 + d * A ^ 2 := by linarith
    have hAB : 0 < A ^ 2 + B ^ 2 := by
      by_contra h
      have hA : A ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
      have hB : B ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
      rw [hA, hB] at hD'; simp at hD'
    have hprod : 0 < (c * ξ₁ ^ 2 + d * ξ₂ ^ 2) * (A ^ 2 + B ^ 2) := by
      rw [hid]; exact mul_pos hD' hξpos
    have := pos_of_mul_pos_left hprod hAB.le
    nlinarith [sq_nonneg ζ₁, sq_nonneg ζ₂]
  · -- `P ≠ 0`: Cauchy–Schwarz and completing the square
    have hcs : (A * ξ₁ + B * ξ₂) ^ 2 ≤ R * (ζ₁ ^ 2 + ζ₂ ^ 2) := by
      have : (A * ξ₁ + B * ξ₂) = -(P₁ * ζ₁ + P₂ * ζ₂) := by linarith
      rw [this, neg_sq, hR]
      nlinarith [sq_nonneg (P₁ * ζ₂ - P₂ * ζ₁)]
    set α := A ^ 2 + R * c with hα
    have hαpos : 0 < α := by rw [hα]; nlinarith [sq_nonneg A, mul_pos hRpos hc]
    have hM : 0 < (A * ξ₁ + B * ξ₂) ^ 2 + R * c * ξ₁ ^ 2 + R * d * ξ₂ ^ 2 := by
      have hkey : α * ((A * ξ₁ + B * ξ₂) ^ 2 + R * c * ξ₁ ^ 2 + R * d * ξ₂ ^ 2) =
          (α * ξ₁ + A * B * ξ₂) ^ 2 + R * ((R * c * d + c * B ^ 2 + d * A ^ 2)) * ξ₂ ^ 2 := by
        rw [hα]; ring
      have hRD : 0 < R * (R * c * d + c * B ^ 2 + d * A ^ 2) := by
        apply mul_pos hRpos; rw [hR]; linarith
      by_cases h2 : ξ₂ = 0
      · have h1 : ξ₁ ≠ 0 := by intro h; exact hξ ⟨h, h2⟩
        rw [h2]
        have := sq_pos_of_ne_zero h1
        nlinarith [sq_nonneg A]
      · have hpos : 0 < α * ((A * ξ₁ + B * ξ₂) ^ 2 + R * c * ξ₁ ^ 2 + R * d * ξ₂ ^ 2) := by
          rw [hkey]; have := sq_pos_of_ne_zero h2
          nlinarith [sq_nonneg (α * ξ₁ + A * B * ξ₂), mul_pos hRD this]
        exact pos_of_mul_pos_right hpos hαpos.le
    have hRQ : 0 < R * (ζ₁ ^ 2 + ζ₂ ^ 2 + c * ξ₁ ^ 2 + d * ξ₂ ^ 2) := by nlinarith
    exact pos_of_mul_pos_right hRQ hRpos.le

/-- A function affine in each variable separately, positive at the four corners of a box,
is positive on the box. -/
theorem bilinear_pos {k p q c₀ c₁ d₀ d₁ c d : ℝ} (hc : c₀ ≤ c ∧ c ≤ c₁) (hd : d₀ ≤ d ∧ d ≤ d₁)
    (h00 : 0 < k * c₀ * d₀ + p * c₀ + q * d₀) (h01 : 0 < k * c₀ * d₁ + p * c₀ + q * d₁)
    (h10 : 0 < k * c₁ * d₀ + p * c₁ + q * d₀) (h11 : 0 < k * c₁ * d₁ + p * c₁ + q * d₁) :
    0 < k * c * d + p * c + q * d := by
  -- affine in `d` at `c₀` and at `c₁`
  have hd' : d₀ < d₁ ∨ d₀ = d₁ := lt_or_eq_of_le (hd.1.trans hd.2)
  have g : ∀ c' : ℝ, 0 < k * c' * d₀ + p * c' + q * d₀ → 0 < k * c' * d₁ + p * c' + q * d₁ →
      0 < k * c' * d + p * c' + q * d := by
    intro c' h0 h1
    rcases hd' with hlt | heq
    · have hw : (d₁ - d₀) * (k * c' * d + p * c' + q * d) =
          (d₁ - d) * (k * c' * d₀ + p * c' + q * d₀) + (d - d₀) * (k * c' * d₁ + p * c' + q * d₁) := by
        ring
      have : 0 < (d₁ - d₀) * (k * c' * d + p * c' + q * d) := by
        rw [hw]
        rcases eq_or_lt_of_le hd.2 with h | h
        · rw [h]; nlinarith
        · nlinarith [mul_pos (sub_pos.mpr h) h0, mul_nonneg (sub_nonneg.mpr hd.1) h1.le]
      exact pos_of_mul_pos_right this (by linarith)
    · have : d = d₀ := le_antisymm (heq ▸ hd.2) hd.1
      rw [this]; exact h0
  have hA := g c₀ h00 h01
  have hB := g c₁ h10 h11
  rcases lt_or_eq_of_le (hc.1.trans hc.2) with hlt | heq
  · have hw : (c₁ - c₀) * (k * c * d + p * c + q * d) =
        (c₁ - c) * (k * c₀ * d + p * c₀ + q * d) + (c - c₀) * (k * c₁ * d + p * c₁ + q * d) := by
      ring
    have : 0 < (c₁ - c₀) * (k * c * d + p * c + q * d) := by
      rw [hw]
      rcases eq_or_lt_of_le hc.2 with h | h
      · rw [h]; nlinarith
      · nlinarith [mul_pos (sub_pos.mpr h) hA, mul_nonneg (sub_nonneg.mpr hc.1) hB.le]
    exact pos_of_mul_pos_right this (by linarith)
  · have : c = c₀ := le_antisymm (heq ▸ hc.2) hc.1
    rw [this]; exact hA

/-- Corner value of the reduced determinant
`D = r² c d + c V₂² + d V₁²` at `c = V₁₁ + σ r |sinh 2x₁|/2`, `d = V₂₂ + τ r |sin 2x₂|/2`. -/
def cornerD (c x₁ x₂ σ τ : ℝ) : ℝ :=
  let r := Real.sqrt (-2 * Vh c x₁ x₂)
  let cc := V11 c x₁ + σ * r * |Real.sinh (2 * x₁)| / 2
  let dd := V22 c x₂ + τ * r * |Real.sin (2 * x₂)| / 2
  r ^ 2 * cc * dd + cc * V2 c x₂ ^ 2 + dd * V1 c x₁ ^ 2

/-- The θ-free analytic estimate behind Theorem 9.4(ii) on the left Hill box. -/
def HessEstimate : Prop :=
  ∀ c x₁ x₂ : ℝ, 2 < c → |x₂| ≤ Real.pi / 2 → Real.cosh x₁ ^ 2 ≤ 2 * c → Vh c x₁ x₂ ≤ 0 →
    0 < V11 c x₁ - Real.sqrt (-2 * Vh c x₁ x₂) * |Real.sinh (2 * x₁)| / 2 ∧
    ∀ σ τ : ℝ, (σ = 1 ∨ σ = -1) → (τ = 1 ∨ τ = -1) → 0 < cornerD c x₁ x₂ σ τ

theorem tangential_hessian_of_estimate (hE : HessEstimate) (c : ℝ) (hc : 2 < c) (s : Phase)
    (hs : ehLeftHamiltonian (1 / 2) c s = 0)
    (h1 : |s 1| ≤ Real.pi / 2) (h0 : Real.cosh (s 0) ^ 2 ≤ 2 * c)
    (v : Phase) (hv : v ≠ 0) (htan : fderiv ℝ (ehLeftHamiltonian (1 / 2) c) s v = 0) :
    0 < fderiv ℝ (fun x => fderiv ℝ (ehLeftHamiltonian (1 / 2) c) x v) s v := by
  rw [hess_Ghalf]
  rw [fderiv_Ghalf] at htan
  rw [G_half_eq] at hs
  set P₁ := s 2 + Real.sin (2 * s 1) / 8
  set P₂ := s 3 + Real.sinh (2 * s 0) / 8
  set R := P₁ ^ 2 + P₂ ^ 2 with hRdef
  have hR : R = -2 * Vh c (s 0) (s 1) := by rw [hRdef]; linarith
  have hV : Vh c (s 0) (s 1) ≤ 0 := by nlinarith [sq_nonneg P₁, sq_nonneg P₂]
  obtain ⟨hcm, hcorner⟩ := hE c (s 0) (s 1) hc h1 h0 hV
  set r := Real.sqrt (-2 * Vh c (s 0) (s 1)) with hr
  have hr2 : r ^ 2 = R := by rw [hr, Real.sq_sqrt (by linarith), hR]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hP1 : |P₁| ≤ r := by
    apply abs_le_of_sq_le_sq _ hr0  -- |P₁|² ≤ r²
    rw [hr2]; nlinarith [sq_nonneg P₂]
  have hP2 : |P₂| ≤ r := by
    apply abs_le_of_sq_le_sq _ hr0
    rw [hr2]; nlinarith [sq_nonneg P₁]
  set α := |Real.sinh (2 * s 0)| / 2
  set β := |Real.sin (2 * s 1)| / 2
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  set cθ := P₂ * (Real.sinh (2 * s 0) / 2) + V11 c (s 0) with hcθdef
  set dθ := -P₁ * (Real.sin (2 * s 1) / 2) + V22 c (s 1) with hdθdef
  have hcθ : V11 c (s 0) - r * α ≤ cθ ∧ cθ ≤ V11 c (s 0) + r * α := by
    have hab : |Real.sinh (2 * s 0) / 2| = α := by rw [abs_div, abs_two]
    have : |P₂ * (Real.sinh (2 * s 0) / 2)| ≤ r * α := by
      rw [abs_mul, hab]; exact mul_le_mul_of_nonneg_right hP2 hα0
    have h' := abs_le.mp this
    constructor <;> linarith [h'.1, h'.2, hcθdef]
  have hdθ : V22 c (s 1) - r * β ≤ dθ ∧ dθ ≤ V22 c (s 1) + r * β := by
    have hab : |Real.sin (2 * s 1) / 2| = β := by rw [abs_div, abs_two]
    have : |-P₁ * (Real.sin (2 * s 1) / 2)| ≤ r * β := by
      rw [abs_mul, abs_neg, hab]; exact mul_le_mul_of_nonneg_right hP1 hβ0
    have h' := abs_le.mp this
    constructor <;> linarith [h'.1, h'.2, hdθdef]
  have hcpos : 0 < cθ := by
    have : V11 c (s 0) - r * α = V11 c (s 0) - Real.sqrt (-2 * Vh c (s 0) (s 1)) *
        |Real.sinh (2 * s 0)| / 2 := by rw [hr]; ring
    linarith [hcθ.1]
  have hcorner' : ∀ σ τ : ℝ, (σ = 1 ∨ σ = -1) → (τ = 1 ∨ τ = -1) →
      0 < R * (V11 c (s 0) + σ * (r * α)) * (V22 c (s 1) + τ * (r * β)) +
        V2 c (s 1) ^ 2 * (V11 c (s 0) + σ * (r * α)) +
        V1 c (s 0) ^ 2 * (V22 c (s 1) + τ * (r * β)) := by
    intro σ τ hσ hτ
    have := hcorner σ τ hσ hτ
    simp only [cornerD] at this
    rw [← hr, hr2] at this
    have e1 : σ * r * |Real.sinh (2 * s 0)| / 2 = σ * (r * α) := by ring
    have e2 : τ * r * |Real.sin (2 * s 1)| / 2 = τ * (r * β) := by ring
    rw [e1, e2] at this
    linarith
  have hD : 0 < R * cθ * dθ + V2 c (s 1) ^ 2 * cθ + V1 c (s 0) ^ 2 * dθ := by
    have := bilinear_pos (k := R) (p := V2 c (s 1) ^ 2) (q := V1 c (s 0) ^ 2)
      (c₀ := V11 c (s 0) - r * α) (c₁ := V11 c (s 0) + r * α)
      (d₀ := V22 c (s 1) - r * β) (d₁ := V22 c (s 1) + r * β) hcθ hdθ
      (by have := hcorner' (-1) (-1) (Or.inr rfl) (Or.inr rfl); linarith)
      (by have := hcorner' (-1) 1 (Or.inr rfl) (Or.inl rfl); linarith)
      (by have := hcorner' 1 (-1) (Or.inl rfl) (Or.inr rfl); linarith)
      (by have := hcorner' 1 1 (Or.inl rfl) (Or.inl rfl); linarith)
    exact this
  have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ (v 2 + Real.cos (2 * s 1) / 4 * v 1) ≠ 0 ∨
      (v 3 + Real.cosh (2 * s 0) / 4 * v 0) ≠ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    apply hv
    funext i
    fin_cases i <;> simp
    · exact a0
    · exact a1
    · rw [a1] at a2; simpa using a2
    · rw [a0] at a3; simpa using a3
  have := quad_pos_of_det (P₁ := P₁) (P₂ := P₂) (A := V1 c (s 0)) (B := V2 c (s 1))
    (c := cθ) (d := dθ) (ξ₁ := v 0) (ξ₂ := v 1)
    (ζ₁ := v 2 + Real.cos (2 * s 1) / 4 * v 1) (ζ₂ := v 3 + Real.cosh (2 * s 0) / 4 * v 0)
    hcpos (by rw [← hRdef]; linarith) (by unfold E1 at htan; exact htan) hne
  unfold E2
  exact this

theorem poly_H1 {a : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    (hW : 0 ≤ 1 - 2 * (a ^ 2 / 2 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32)) :
    0 ≤ 2 * a ^ 2 - 1 - a / 2 - (2 * (2 * a ^ 2 - 1) ^ 2 - 1) / 16 ∧
    (1 - 2 * (a ^ 2 / 2 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32)) * (a ^ 2 * (a ^ 2 - 1)) ≤
      (2 * a ^ 2 - 1 - a / 2 - (2 * (2 * a ^ 2 - 1) ^ 2 - 1) / 16) ^ 2 := by
  have h1 : 0 ≤ a - 1 := by linarith
  have h2 : 0 ≤ 2 - a := by linarith
  -- the Hill constraint forces `a ≤ 1.81`
  have h3 : a ≤ 181 / 100 := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) h1]
  have h4 : 0 ≤ 181 / 100 - a := by linarith
  constructor
  · nlinarith [mul_nonneg h1 h4, mul_nonneg (mul_nonneg h1 h4) h1, mul_nonneg (mul_nonneg h1 h4) h4]
  · nlinarith [mul_nonneg h1 h4, mul_nonneg (mul_nonneg h1 h4) h1, mul_nonneg (mul_nonneg h1 h4) h4,
      mul_nonneg (mul_nonneg h1 h1) (mul_nonneg h1 h4), mul_nonneg (mul_nonneg h4 h4) (mul_nonneg h1 h4)]

/-- (H1): the worst-case `c_θ` is positive on the left Hill box, for every `c > 2`. -/
theorem cmin_pos {c x₁ x₂ : ℝ} (hc : 2 < c) (h2 : |x₂| ≤ Real.pi / 2)
    (h0 : Real.cosh x₁ ^ 2 ≤ 2 * c) (hV : Vh c x₁ x₂ ≤ 0) :
    0 < V11 c x₁ - Real.sqrt (-2 * Vh c x₁ x₂) * |Real.sinh (2 * x₁)| / 2 := by
  set a := Real.cosh x₁ with ha
  set b := Real.cos x₂ with hb
  have ha1 : 1 ≤ a := Real.one_le_cosh x₁
  have ha2 : a ≤ 2 := cosh_le_two hc h0 hV
  have hb0 : 0 ≤ b := cos_nonneg_of_abs_le h2
  have hb1 : b ≤ 1 := Real.cos_le_one x₂
  have hsh : Real.sinh x₁ ^ 2 = a ^ 2 - 1 := by rw [ha, Real.cosh_sq]; ring
  -- the potential at `c = 2` splits, and the `x₂`-part is at least `-1/2`
  have hV2 : Vh 2 x₁ x₂ = (a ^ 2 / 2 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32) +
      (-(b ^ 2) / 2 - b ^ 2 * (1 - b ^ 2) / 32) := by
    unfold Vh; rw [sinh_two_sq, sin_two_sq]; ring
  have hlo := poly_V2_lo hb0 hb1
  have hmono : Vh 2 x₁ x₂ ≤ Vh c x₁ x₂ := by
    rw [Vh_eq c]; have := cos_sq_le_cosh_sq x₁ x₂; nlinarith
  set ρ2 := 1 - 2 * (a ^ 2 / 2 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32) with hρ2
  have hR : -2 * Vh c x₁ x₂ ≤ ρ2 := by rw [hρ2]; nlinarith
  have hρ0 : 0 ≤ ρ2 := by linarith
  obtain ⟨hq0, hqsq⟩ := poly_H1 ha1 ha2 hρ0
  have hsq : Real.sqrt (-2 * Vh c x₁ x₂) ≤ Real.sqrt ρ2 := Real.sqrt_le_sqrt hR
  have hsinh2 : |Real.sinh (2 * x₁)| / 2 = a * |Real.sinh x₁| := by
    rw [Real.sinh_two_mul, abs_mul, abs_mul, abs_two, abs_of_pos (Real.cosh_pos x₁)]; ring
  have hkey : Real.sqrt ρ2 * (a * |Real.sinh x₁|) ≤
      2 * a ^ 2 - 1 - a / 2 - (2 * (2 * a ^ 2 - 1) ^ 2 - 1) / 16 := by
    apply (abs_le_of_sq_le_sq' _ hq0).2
    rw [mul_pow, mul_pow, Real.sq_sqrt hρ0, sq_abs, hsh]
    exact hqsq
  have hV11 : V11 c x₁ = (2 * a ^ 2 - 1 - a / 2 - (2 * (2 * a ^ 2 - 1) ^ 2 - 1) / 16) +
      (c - 2) * (2 * a ^ 2 - 1) / 2 := by
    unfold V11
    rw [show (4 : ℝ) * x₁ = 2 * (2 * x₁) by ring, Real.cosh_two_mul (2 * x₁), sinh_two_sq,
      Real.cosh_two_mul x₁, Real.sinh_sq, ← ha]
    ring
  have hpos : 0 < (c - 2) * (2 * a ^ 2 - 1) / 2 := by
    have : 0 < 2 * a ^ 2 - 1 := by nlinarith
    have : 0 < c - 2 := by linarith
    positivity
  have hprod : Real.sqrt (-2 * Vh c x₁ x₂) * |Real.sinh (2 * x₁)| / 2 ≤
      Real.sqrt ρ2 * (a * |Real.sinh x₁|) := by
    rw [mul_div_assoc, hsinh2]
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  rw [hV11]
  linarith

theorem hessEstimate_of_corner : HessEstimate := by
  intro c x₁ x₂ hc h2 h0 hV
  refine ⟨cmin_pos hc h2 h0 hV, fun σ τ hσ hτ => ?_⟩
  exact eh_half_mass_corner_determinant_pos c x₁ x₂ σ τ hc h2 h0 hV hσ hτ

end

end EHConvex

end BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (c : ℝ) (hc : 2 < c) (s : Phase)
    (hs : ehLeftHamiltonian (1 / 2) c s = 0)
    (h1 : |s 1| ≤ Real.pi / 2) (h0 : Real.cosh (s 0) ^ 2 ≤ 2 * c)
    (v : Phase) (hv : v ≠ 0) (htan : fderiv ℝ (ehLeftHamiltonian (1 / 2) c) s v = 0) :
    0 < fderiv ℝ (fun x => fderiv ℝ (ehLeftHamiltonian (1 / 2) c) x v) s v :=
  EHConvex.tangential_hessian_of_estimate EHConvex.hessEstimate_of_corner c hc s hs h1 h0 v hv htan
