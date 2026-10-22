-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_half_mass_star_shaped
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T13:42:44.916511+00:00
-- url     : https://prove2.me/submissions/b3bc7485-3378-45fd-b085-8380584ded49

import Definitions.Def_BirkhoffGlobalSection_EHConvexPerturbation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Equal-mass star-shapedness: reduction to `c = 2` by monotonicity in the energy, then a
parameter-free estimate split into an `x₁`-part and an `x₂`-part, each a polynomial inequality
after the derivative bounds `0 ≤ g₂ ≤ x sinh² x / 2` and `0 ≤ -g₁ ≤ y sin² y / 2`. -/

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

end

end EHConvex

end BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (c : ℝ) (hc : 2 < c) (s : Phase)
    (hs : ehLeftHamiltonian (1 / 2) c s = 0)
    (h1 : |s 1| ≤ Real.pi / 2) (h0 : Real.cosh (s 0) ^ 2 ≤ 2 * c) :
    0 < fderiv ℝ (ehLeftHamiltonian (1 / 2) c) s s :=
  EHConvex.star_of_critical EHConvex.critical_radial_estimate c hc s hs h1 h0
