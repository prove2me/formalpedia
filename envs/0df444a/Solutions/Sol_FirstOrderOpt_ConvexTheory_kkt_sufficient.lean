-- Prove2me | solution 1 for FirstOrderOpt.ConvexTheory.kkt_sufficient
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T15:49:52.48148+00:00
-- url     : https://prove2.me/submissions/c43732d0-f4cd-40a7-804b-49688ada3489

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

/-! Disproof of e0a3cc39 `FirstOrderOpt.ConvexTheory.kkt_sufficient`.

`normalCone X x = {w | ∀ y ∈ X, ⟪w, y - x⟫ ≤ 0}` is the usual outward normal cone, but the
stationarity hypothesis puts `+(∇f + Σ λᵢ∇gᵢ + Σ yⱼwⱼ)` into it. The correct KKT condition puts the
negative there. With the sign as written, the hypothesis certifies a maximiser. Take `n = 1`,
`m = p = 0`, `v = e₀`, `f x = ⟪v, x⟫`, `X = [0, v]`, `x* = v`. Then `∇f(x*) = v` and
`⟪v, y - v⟫ = (c - 1)‖v‖² ≤ 0` for `y = c v ∈ X`, but `f x* = 1 > 0 = f 0`. -/

set_option autoImplicit false

open FirstOrderOpt.ConvexTheory Gradient in
theorem solution : ¬ (∀ {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (hfdiff : DifferentiableAt ℝ f xstar) (hgdiff : ∀ i, DifferentiableAt ℝ (g i) xstar)
    (hxstar_g : ∀ i, g i xstar ≤ 0) (hxstar_h : ∀ j, h j xstar = 0)
    (lamStar : Fin m → ℝ) (yStar : Fin p → ℝ) (hlamStar : ∀ i, 0 ≤ lamStar i)
    (hstationarity : (∇ f xstar) + (∑ i, lamStar i • ∇ (g i) xstar) + (∑ j, yStar j • w j) ∈
      normalCone X xstar)
    (hcomplementary : ∀ i, lamStar i * g i xstar = 0),
    ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x) := by
  intro H
  set v : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with hv
  have hvv : inner ℝ v v = (1 : ℝ) := by simp [hv]
  have hgradf : HasGradientAt (fun x : EuclideanSpace ℝ (Fin 1) => inner ℝ v x) v v := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hfun : (fun x : EuclideanSpace ℝ (Fin 1) => inner ℝ v x) =
        ⇑(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 1)) v) := by
      funext x
      rw [InnerProductSpace.toDual_apply_apply]
    rw [hfun]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 1)) v).hasFDerivAt
  have hconv : ConvexOn ℝ (segment ℝ 0 v) (fun x : EuclideanSpace ℝ (Fin 1) => inner ℝ v x) := by
    refine ⟨convex_segment 0 v, ?_⟩
    intro x _ y _ a c _ _ _
    simp [inner_add_right, inner_smul_right]
  have key := @H 1 0 0 (segment ℝ 0 v) (fun x => inner ℝ v x) (fun _ _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ _ => 0) (by intro j; exact j.elim0) (convex_segment 0 v) hconv
    (by intro i; exact i.elim0) v (right_mem_segment ℝ 0 v) hgradf.differentiableAt
    (by intro i; exact i.elim0) (by intro i; exact i.elim0) (by intro j; exact j.elim0)
    0 0 (by intro i; exact i.elim0) (by
      rw [hgradf.gradient]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      intro y hy
      obtain ⟨a, c, ha, hc, hac, rfl⟩ := hy
      have : a • (0 : EuclideanSpace ℝ (Fin 1)) + c • v - v = (c - 1) • v := by
        rw [smul_zero, zero_add, sub_smul, one_smul]
      rw [this, inner_smul_right, hvv]
      nlinarith)
    (by intro i; exact i.elim0) 0 (left_mem_segment ℝ 0 v) (by intro i; exact i.elim0)
    (by intro j; exact j.elim0)
  simp only [inner_zero_right, hvv] at key
  norm_num at key
