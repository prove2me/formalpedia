-- Prove2me | solution 1 for ConvexOptAlg.StrongGD.theorem_3_12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:12:47.11199+00:00
-- url     : https://prove2.me/submissions/1540c791-d849-410b-87e1-116166f84d5a

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

set_option autoImplicit false

open scoped InnerProductSpace

theorem sgd_line_deriv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ψ : H → ℝ} (hΨ : Differentiable ℝ Ψ) (x d : H) (t0 : ℝ) :
    HasDerivAt (fun t : ℝ => Ψ (x + t • d)) (inner ℝ (gradient Ψ (x + t0 • d)) d) t0 := by
  have h1 : HasFDerivAt Ψ (InnerProductSpace.toDual ℝ H (gradient Ψ (x + t0 • d))) (x + t0 • d) :=
    (hΨ (x + t0 • d)).hasGradientAt.hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => x + t • d) d t0 := by
    simpa using ((hasDerivAt_id t0).smul_const d).const_add x
  have h3 := h1.comp_hasDerivAt t0 h2
  simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using h3

theorem sgd_descent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ψ : H → ℝ} {L : ℝ} (hΨ : Differentiable ℝ Ψ)
    (hL : ∀ x y : H, ‖gradient Ψ x - gradient Ψ y‖ ≤ L * ‖x - y‖) (x y : H) :
    Ψ y ≤ Ψ x + inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  have hf : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Ψ (x + t • (y - x)))
      (inner ℝ (gradient Ψ (x + t • (y - x))) (y - x)) t :=
    fun t => sgd_line_deriv hΨ x (y - x) t
  have hB : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => Ψ x + t * inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * t ^ 2)
      (inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (2 * t)) t := by
    intro t
    have h1 := ((hasDerivAt_id' t).mul_const (inner ℝ (gradient Ψ x) (y - x))).const_add (Ψ x)
    have h2 := (hasDerivAt_pow 2 t).const_mul (L / 2 * ‖y - x‖ ^ 2)
    have h3 : HasDerivAt
        (fun s : ℝ => Ψ x + s * inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * s ^ 2)
        (1 * inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (↑2 * t ^ (2 - 1))) t :=
      h1.add h2
    exact h3.congr_deriv (by norm_num)
  have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1)
    (f := fun t : ℝ => Ψ (x + t • (y - x)))
    (f' := fun t => inner ℝ (gradient Ψ (x + t • (y - x))) (y - x))
    (B := fun t : ℝ => Ψ x + t * inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * t ^ 2)
    (B' := fun t => inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (2 * t))
    (fun t _ => (hf t).continuousAt.continuousWithinAt)
    (fun t _ => (hf t).hasDerivWithinAt)
    (by simp)
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
    (by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      show inner ℝ (gradient Ψ (x + t • (y - x))) (y - x) ≤
        inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (2 * t)
      have e1 : inner ℝ (gradient Ψ (x + t • (y - x))) (y - x) - inner ℝ (gradient Ψ x) (y - x)
          = inner ℝ (gradient Ψ (x + t • (y - x)) - gradient Ψ x) (y - x) := by
        rw [inner_sub_left]
      have e2 := real_inner_le_norm (gradient Ψ (x + t • (y - x)) - gradient Ψ x) (y - x)
      have e3 := hL (x + t • (y - x)) x
      have e4 : ‖x + t • (y - x) - x‖ = t * ‖y - x‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
      rw [e4] at e3
      have e5 := mul_le_mul_of_nonneg_right e3 (norm_nonneg (y - x))
      nlinarith)
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
  have e6 : x + (1:ℝ) • (y - x) = y := by rw [one_smul]; abel
  simp only [e6, one_mul, one_pow, mul_one] at key
  linarith

/-- Lemma 3.11 (multiplied form), from the strong-convexity and descent inequalities. -/
theorem sgd_key {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (g : H → H) (α β : ℝ) (hab : α ≤ β)
    (hS : ∀ x z : H, f x + inner ℝ (g x) (z - x) + α / 2 * ‖z - x‖ ^ 2 ≤ f z)
    (hD : ∀ y z : H, f z ≤ f y + inner ℝ (g y) (z - y) + β / 2 * ‖z - y‖ ^ 2) (x y : H) :
    α * β * ‖x - y‖ ^ 2 + ‖g x - g y‖ ^ 2 ≤ (α + β) * inner ℝ (g x - g y) (x - y) := by
  set u := x - y with hu
  set v := g x - g y with hv
  set w := α • u - v with hw
  have hs : ∀ s : ℝ, 0 ≤ inner ℝ v u - α * ‖u‖ ^ 2 - 2 * s * ‖w‖ ^ 2
      + (β - α) * s ^ 2 * ‖w‖ ^ 2 := by
    intro s
    have h1 := hS x (y - s • w)
    have h2 := hD y (y - s • w)
    have h3 := hS y (x + s • w)
    have h4 := hD x (x + s • w)
    have e1 : y - s • w - x = -(u + s • w) := by rw [hu]; abel
    have e2 : y - s • w - y = -(s • w) := by abel
    have e3 : x + s • w - y = u + s • w := by rw [hu]; abel
    have e4 : x + s • w - x = s • w := by abel
    rw [e1, norm_neg] at h1
    rw [e2, norm_neg] at h2
    rw [e3] at h3
    rw [e4] at h4
    have n1 : ‖u + s • w‖ ^ 2 = ‖u‖ ^ 2 + 2 * (s * inner ℝ u w) + s ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
    have n2 : ‖s • w‖ ^ 2 = s ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [n1] at h1 h3
    rw [n2] at h2 h4
    rw [inner_neg_right, inner_add_right, real_inner_smul_right] at h1
    rw [inner_neg_right, real_inner_smul_right] at h2
    rw [inner_add_right, real_inner_smul_right] at h3
    rw [real_inner_smul_right] at h4
    have i1 : inner ℝ v u = inner ℝ (g x) u - inner ℝ (g y) u := by rw [hv, inner_sub_left]
    have i2 : inner ℝ v w = inner ℝ (g x) w - inner ℝ (g y) w := by rw [hv, inner_sub_left]
    have i3 : ‖w‖ ^ 2 = α * inner ℝ u w - inner ℝ v w := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => rw [hw]
      rw [inner_sub_left, real_inner_smul_left]
    have i3' : 2 * s * ‖w‖ ^ 2 = 2 * s * (α * inner ℝ u w - inner ℝ v w) := by rw [i3]
    have i2' : s * inner ℝ v w = s * inner ℝ (g x) w - s * inner ℝ (g y) w := by rw [i2]; ring
    rw [i1]
    linarith
  have hW0 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hid : (α + β) * inner ℝ v u - α * β * ‖u‖ ^ 2 - ‖v‖ ^ 2
      = (β - α) * (inner ℝ v u - α * ‖u‖ ^ 2) - ‖w‖ ^ 2 := by
    have : ‖w‖ ^ 2 = α ^ 2 * ‖u‖ ^ 2 - 2 * α * inner ℝ v u + ‖v‖ ^ 2 := by
      rw [hw, norm_sub_sq_real, norm_smul, real_inner_smul_left, mul_pow, Real.norm_eq_abs,
        sq_abs, real_inner_comm]
      ring
    rw [this]; ring
  have goal' : 0 ≤ (β - α) * (inner ℝ v u - α * ‖u‖ ^ 2) - ‖w‖ ^ 2 := by
    rcases lt_or_eq_of_le hab with hlt | heq
    · have hL : 0 < β - α := sub_pos.2 hlt
      have h := hs (1 / (β - α))
      have h' := mul_nonneg hL.le h
      have e : (β - α) * (inner ℝ v u - α * ‖u‖ ^ 2 - 2 * (1 / (β - α)) * ‖w‖ ^ 2
          + (β - α) * (1 / (β - α)) ^ 2 * ‖w‖ ^ 2)
          = (β - α) * (inner ℝ v u - α * ‖u‖ ^ 2) - ‖w‖ ^ 2 := by
        field_simp
        ring
      rw [e] at h'
      exact h'
    · have hL : β - α = 0 := by rw [heq]; ring
      rw [hL, zero_mul, zero_sub, neg_nonneg]
      by_contra hc
      push_neg at hc
      have h := hs ((inner ℝ v u - α * ‖u‖ ^ 2 + 1) / (2 * ‖w‖ ^ 2))
      rw [hL] at h
      have e : 2 * ((inner ℝ v u - α * ‖u‖ ^ 2 + 1) / (2 * ‖w‖ ^ 2)) * ‖w‖ ^ 2
          = inner ℝ v u - α * ‖u‖ ^ 2 + 1 := by
        have hwn : ‖w‖ ≠ 0 := by
          intro h0; rw [h0] at hc; simp at hc
        field_simp
      linarith
  have hvu : inner ℝ (g x - g y) (x - y) = inner ℝ v u := rfl
  rw [hvu]
  linarith

/- Theorem 3.12, p. 279: the exponential value bound for fixed-step gradient descent. -/
open ConvexOptAlg.StrongGD in
theorem solution {n : ℕ} (hn : 0 < n) (f : E n → ℝ)
    (g : E n → E n) (α β : ℝ) (hα : 0 < α)
    (hsm : IsBetaSmooth f g β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (xstar : E n) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → E n) (hrun : IsGDRun g (2 / (α + β)) x) :
    ∀ t : ℕ,
      f (x (t + 1)) - f xstar ≤
        (β / 2) * Real.exp (-(4 * (t : ℝ) / (β / α + 1))) * ‖x 1 - xstar‖ ^ 2 := by
  obtain ⟨hgrad, hβ0, hlip⟩ := hsm
  have hgr : ∀ z, gradient f z = g z := fun z => (hgrad z).gradient
  have hdiff : Differentiable ℝ f := fun z => (hgrad z).differentiableAt
  have hD : ∀ y z : E n, f z ≤ f y + inner ℝ (g y) (z - y) + β / 2 * ‖z - y‖ ^ 2 := by
    intro y z
    have := sgd_descent (L := β) hdiff (by intro a b; rw [hgr, hgr]; exact hlip a b) y z
    rwa [hgr] at this
  have hS : ∀ x z : E n, f x + inner ℝ (g x) (z - x) + α / 2 * ‖z - x‖ ^ 2 ≤ f z := by
    intro a b
    exact hsc a (Set.mem_univ a) b (Set.mem_univ b)
  -- α ≤ β
  have hab : α ≤ β := by
    set e : E n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)
    have he : ‖e‖ = 1 := by simp [e]
    have h1 := hS 0 e
    have h2 := hD 0 e
    rw [sub_zero, he] at h1 h2
    linarith
  -- gradient vanishes at the minimizer
  have hg0 : g xstar = 0 := by
    set s : ℝ := 1 / (β + 1)
    have hs0 : 0 < s := by positivity
    have hsβ : β * s ≤ 1 := by
      have : β * s = β / (β + 1) := by simp [s]; ring
      rw [this, div_le_one (by linarith)]; linarith
    have h1 := hD xstar (xstar - s • g xstar)
    have h2 : f xstar ≤ f (xstar - s • g xstar) := hstar (Set.mem_univ _)
    have e1 : xstar - s • g xstar - xstar = -(s • g xstar) := by abel
    rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, real_inner_self_eq_norm_sq] at h1
    have hG : 0 ≤ ‖g xstar‖ ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right hsβ (mul_nonneg hs0.le hG)
    have h4 : s * ‖g xstar‖ ^ 2 ≤ 0 := by nlinarith
    have h5 : ‖g xstar‖ ^ 2 ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith [mul_pos hs0 hc]
    have h6 : ‖g xstar‖ = 0 := by nlinarith [norm_nonneg (g xstar)]
    exact norm_eq_zero.1 h6
  have hS0 : 0 < α + β := by linarith
  set η : ℝ := 2 / (α + β) with hη
  set r : ℝ := ((β - α) / (α + β)) ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hrη : r = 1 - η ^ 2 * α * β := by
    rw [hr, hη]; field_simp; ring
  -- one-step contraction
  have hstep : ∀ t : ℕ, 1 ≤ t → ‖x (t + 1) - xstar‖ ^ 2 ≤ r * ‖x t - xstar‖ ^ 2 := by
    intro t ht
    have hk := sgd_key f g α β hab hS hD (x t) xstar
    rw [hg0, sub_zero] at hk
    rw [hrun t ht]
    have e : x t - η • g (x t) - xstar = (x t - xstar) - η • g (x t) := by abel
    rw [e, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_smul_right, real_inner_comm]
    have hηS : η * (α + β) = 2 := by rw [hη]; field_simp
    have hη2 : 0 ≤ η ^ 2 := by positivity
    have h5 := mul_le_mul_of_nonneg_left hk hη2
    rw [hrη]
    have e2 : η ^ 2 * ((α + β) * inner ℝ (g (x t)) (x t - xstar))
        = 2 * η * inner ℝ (g (x t)) (x t - xstar) := by
      rw [← mul_assoc, pow_two, mul_assoc η η, hηS]; ring
    rw [e2] at h5
    nlinarith
  have hiter : ∀ k : ℕ, ‖x (k + 1) - xstar‖ ^ 2 ≤ r ^ k * ‖x 1 - xstar‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hstep (k + 1) (by omega)
      calc ‖x (k + 1 + 1) - xstar‖ ^ 2 ≤ r * ‖x (k + 1) - xstar‖ ^ 2 := this
        _ ≤ r * (r ^ k * ‖x 1 - xstar‖ ^ 2) := mul_le_mul_of_nonneg_left ih hr0
        _ = r ^ (k + 1) * ‖x 1 - xstar‖ ^ 2 := by ring
  -- value bound
  have hval : ∀ z : E n, f z - f xstar ≤ β / 2 * ‖z - xstar‖ ^ 2 := by
    intro z
    have := hD xstar z
    rw [hg0, inner_zero_left] at this
    linarith
  -- r^t ≤ exp(...)
  set c : ℝ := 2 * α / (α + β) with hc
  have hc1 : 1 - c = (β - α) / (α + β) := by rw [hc]; field_simp; ring
  have hc0 : 0 ≤ 1 - c := by rw [hc1]; exact div_nonneg (by linarith) hS0.le
  have hexp : ∀ t : ℕ, r ^ t ≤ Real.exp (-(4 * (t : ℝ) / (β / α + 1))) := by
    intro t
    have h1 : 1 - c ≤ Real.exp (-c) := by linarith [Real.add_one_le_exp (-c)]
    have h2 : r ≤ Real.exp (-c) ^ 2 := by
      rw [hr, ← hc1]; exact pow_le_pow_left₀ hc0 h1 2
    have h3 : r ^ t ≤ (Real.exp (-c) ^ 2) ^ t := pow_le_pow_left₀ hr0 h2 t
    have h4 : (Real.exp (-c) ^ 2) ^ t = Real.exp (-(4 * (t : ℝ) / (β / α + 1))) := by
      rw [← pow_mul, ← Real.exp_nat_mul]
      congr 1
      rw [hc]
      push_cast
      have hα0 : α ≠ 0 := hα.ne'
      have h' : β / α + 1 = (α + β) / α := by field_simp; ring
      rw [h']
      field_simp
      ring
    linarith
  intro t
  have hb2 : 0 ≤ β / 2 := by linarith
  calc f (x (t + 1)) - f xstar ≤ β / 2 * ‖x (t + 1) - xstar‖ ^ 2 := hval _
    _ ≤ β / 2 * (r ^ t * ‖x 1 - xstar‖ ^ 2) := mul_le_mul_of_nonneg_left (hiter t) hb2
    _ ≤ β / 2 * (Real.exp (-(4 * (t : ℝ) / (β / α + 1))) * ‖x 1 - xstar‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hb2
        exact mul_le_mul_of_nonneg_right (hexp t) (by positivity)
    _ = (β / 2) * Real.exp (-(4 * (t : ℝ) / (β / α + 1))) * ‖x 1 - xstar‖ ^ 2 := by ring
