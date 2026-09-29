-- Prove2me | solution 1 for FirstOrderOpt.ConvexTheory.kkt_necessary
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T18:47:27.916311+00:00
-- url     : https://prove2.me/submissions/8969d00c-eb28-40b4-91da-bb789bab2d14

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

/-! Disproof of e0d3948a `FirstOrderOpt.ConvexTheory.kkt_necessary`.

`normalCone X x = {w | ∀ y ∈ X, ⟪w, y - x⟫ ≤ 0}` is the usual (outward) normal cone, but the
conclusion puts `+(∇f + Σ λᵢ∇gᵢ + Σ yⱼwⱼ)` into it; the correct KKT condition puts the negative
there. Take `n = 1`, `m = p = 0`, `v = e₀`, `f x = ⟪v, x⟫`, `X = {y | 0 ≤ ⟪v, y⟫}` (closed convex
half-line), `x̄ = v ∈ interior X ⊆ intrinsicInterior X`, `x* = 0` (a minimiser of `f` on `X`).
The conclusion would give `∇f(0) = v ∈ normalCone X 0`, i.e. `⟪v, y⟫ ≤ 0` for all `y ∈ X`; at
`y = v` this reads `1 ≤ 0`. -/

set_option autoImplicit false

open FirstOrderOpt.ConvexTheory Gradient in
theorem solution : ¬ (∀ {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (barx : EuclideanSpace ℝ (Fin n)) (hbarx_ri : barx ∈ intrinsicInterior ℝ X)
    (hbarx_g : ∀ i, g i barx < 0) (hbarx_h : ∀ j, h j barx = 0)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (hfdiff : DifferentiableAt ℝ f xstar) (hgdiff : ∀ i, DifferentiableAt ℝ (g i) xstar)
    (hxstar_g : ∀ i, g i xstar ≤ 0) (hxstar_h : ∀ j, h j xstar = 0)
    (hxstar_opt : ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x),
    ∃ lamStar : Fin m → ℝ, ∃ yStar : Fin p → ℝ, (∀ i, 0 ≤ lamStar i) ∧
      (∇ f xstar) + (∑ i, lamStar i • ∇ (g i) xstar) + (∑ j, yStar j • w j) ∈
        normalCone X xstar ∧
      (∀ i, lamStar i * g i xstar = 0)) := by
  intro H
  set v : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with hv
  have hvv : inner ℝ v v = (1 : ℝ) := by simp [hv]
  have hgradf : HasGradientAt (fun x : EuclideanSpace ℝ (Fin 1) => inner ℝ v x) v 0 := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hfun : (fun x : EuclideanSpace ℝ (Fin 1) => inner ℝ v x) =
        ⇑(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 1)) v) := by
      funext x
      rw [InnerProductSpace.toDual_apply_apply]
    rw [hfun]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 1)) v).hasFDerivAt
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 1) => inner ℝ v y) :=
    continuous_const.inner continuous_id
  have hXconv : Convex ℝ {y : EuclideanSpace ℝ (Fin 1) | 0 ≤ inner ℝ v y} := by
    intro x hx y hy a c ha hc _
    simp only [Set.mem_setOf_eq, inner_add_right, inner_smul_right] at hx hy ⊢
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hc hy)
  have hXclosed : IsClosed {y : EuclideanSpace ℝ (Fin 1) | 0 ≤ inner ℝ v y} :=
    isClosed_le continuous_const hcont
  have hfconv : ConvexOn ℝ {y : EuclideanSpace ℝ (Fin 1) | 0 ≤ inner ℝ v y}
      (fun x : EuclideanSpace ℝ (Fin 1) => inner ℝ v x) := by
    refine ⟨hXconv, ?_⟩
    intro x _ y _ a c _ _ _
    simp [inner_add_right, inner_smul_right]
  have hvX : v ∈ {y : EuclideanSpace ℝ (Fin 1) | 0 ≤ inner ℝ v y} := by
    simp only [Set.mem_setOf_eq, hvv]
    norm_num
  have hvint : v ∈ interior {y : EuclideanSpace ℝ (Fin 1) | 0 ≤ inner ℝ v y} :=
    interior_maximal (fun y (hy : 0 < inner ℝ v y) => le_of_lt hy)
      (isOpen_lt continuous_const hcont) (show (0 : ℝ) < inner ℝ v v by rw [hvv]; norm_num)
  have h0X : (0 : EuclideanSpace ℝ (Fin 1)) ∈ {y : EuclideanSpace ℝ (Fin 1) | 0 ≤ inner ℝ v y} := by
    simp
  obtain ⟨lam, y, _, hN, _⟩ := @H 1 0 0 {y : EuclideanSpace ℝ (Fin 1) | 0 ≤ inner ℝ v y}
    (fun x => inner ℝ v x) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
    (by intro j; exact j.elim0) hXconv hXclosed hfconv (by intro i; exact i.elim0)
    v (interior_subset_intrinsicInterior hvint) (by intro i; exact i.elim0)
    (by intro j; exact j.elim0) 0 h0X hgradf.differentiableAt (by intro i; exact i.elim0)
    (by intro i; exact i.elim0) (by intro j; exact j.elim0)
    (fun x hx _ _ => by simpa using hx)
  rw [hgradf.gradient] at hN
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hN
  have := hN v hvX
  rw [sub_zero, hvv] at this
  norm_num at this
