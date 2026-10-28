-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.le_exp_mul_of_hasDerivAt_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:27.218988+00:00
-- url     : https://prove2.me/submissions/151c1a75-ec65-4f93-a04d-c2443cad00aa

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- The derivative of `r ↦ e^{-c r} E r`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_exp_neg_mul_mul {E : ℝ → ℝ} {e c s : ℝ} (hE : HasDerivAt E e s) :
    HasDerivAt (fun r => Real.exp (-(c * r)) * E r)
      (Real.exp (-(c * s)) * (e - c * E s)) s := by
  have h1 : HasDerivAt (fun r : ℝ => -(c * r)) (-c) s := by
    simpa only [mul_one] using
      ((hasDerivAt_id' s).const_mul c).fun_neg
  have h2 := h1.exp
  exact (h2.fun_mul hE).congr_deriv (by ring)
/-- Grönwall on `[0, ∞)`: if `E` is continuous on `[0, ∞)` with `E'(s) ≤ c E(s)` for `s > 0`, then
`E t ≤ e^{c t} E 0` for `t ≥ 0`. -/
theorem solution {E E' : ℝ → ℝ} {c : ℝ} (hc : ContinuousOn E (Ici 0))
    (hd : ∀ s, 0 < s → HasDerivAt E (E' s) s) (hle : ∀ s, 0 < s → E' s ≤ c * E s) {t : ℝ}
    (ht : 0 ≤ t) :
    E t ≤ Real.exp (c * t) * E 0 := by
  let G : ℝ → ℝ := fun r => Real.exp (-(c * r)) * E r

  have hG : ContinuousOn G (Ici 0) := by
    dsimp [G]
    exact
      (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)).continuousOn.mul hc

  have hanti : AntitoneOn G (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Ici 0)
      (f := G)
      (f' := fun x => Real.exp (-(c * x)) * (E' x - c * E x))
      (convex_Ici (0 : ℝ)) hG ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx
      simpa [G] using
        (FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_exp_neg_mul_mul (c := c) (s := x) (hd x hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact
        mul_nonpos_of_nonneg_of_nonpos
          (Real.exp_pos (-(c * x))).le (by
            linarith [hle x hx])

  have hGle : G t ≤ G 0 := by
    exact hanti (show (0 : ℝ) ∈ Ici 0 by simp) (show t ∈ Ici 0 by exact ht) ht

  have hGle' : G t ≤ E 0 := by
    simpa [G] using hGle

  have hrep : E t = Real.exp (c * t) * G t := by
    dsimp [G]
    rw [← mul_assoc, ← Real.exp_add]
    have hzero : c * t + -(c * t) = 0 := by
      ring
    rw [hzero, Real.exp_zero, one_mul]

  calc
    E t = Real.exp (c * t) * G t := hrep
    _ ≤ Real.exp (c * t) * E 0 :=
      mul_le_mul_of_nonneg_left hGle' (Real.exp_pos (c * t)).le
