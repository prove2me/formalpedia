-- Prove2me | solution 1 for FirstOrderOpt.ConvexTheory.kkt_sufficient_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:34:57.642957+00:00
-- url     : https://prove2.me/submissions/76a74cea-72c7-4772-a3eb-03fba8721c0c

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

set_option autoImplicit false

open scoped Gradient RealInnerProductSpace in
lemma af191e75_grad_ineq {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ConvexOn ℝ X F)
    {x0 x : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ X) (hx : x ∈ X)
    (hd : DifferentiableAt ℝ F x0) :
    F x0 + ⟪∇ F x0, x - x0⟫ ≤ F x := by
  let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x0 x
  have hc : ConvexOn ℝ (L ⁻¹' X) (F ∘ L) := hF.comp_affineMap L
  have hL : ∀ t : ℝ, L t = x0 + t • (x - x0) := by
    intro t
    simp only [L, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    abel
  have h0 : (0 : ℝ) ∈ L ⁻¹' X := by simp [Set.mem_preimage, hL, hx0]
  have h1 : (1 : ℝ) ∈ L ⁻¹' X := by simp [Set.mem_preimage, hL, hx]
  have hderL : HasDerivAt (fun t : ℝ => x0 + t • (x - x0)) (x - x0) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (x - x0)).const_add x0
  have hdF : HasFDerivAt F (fderiv ℝ F x0) (x0 + (0:ℝ) • (x - x0)) := by
    simpa using hd.hasFDerivAt
  have hcomp : HasDerivAt (F ∘ L) (fderiv ℝ F x0 (x - x0)) 0 := by
    have := hdF.comp_hasDerivAt (0:ℝ) hderL
    have e : (F ∘ L) = F ∘ (fun t : ℝ => x0 + t • (x - x0)) := by
      funext t; simp [hL]
    rw [e]; exact this
  have key := hc.le_slope_of_hasDerivAt h0 h1 zero_lt_one hcomp
  have hs : slope (F ∘ L) 0 1 = F x - F x0 := by
    simp [slope_def_field, hL]
  have hg : ⟪∇ F x0, x - x0⟫ = fderiv ℝ F x0 (x - x0) := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [hs] at key
  linarith

open FirstOrderOpt.ConvexTheory Gradient in
theorem solution {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (hfdiff : DifferentiableAt ℝ f xstar) (hgdiff : ∀ i, DifferentiableAt ℝ (g i) xstar)
    (hxstar_g : ∀ i, g i xstar ≤ 0) (hxstar_h : ∀ j, h j xstar = 0)
    (lamStar : Fin m → ℝ) (yStar : Fin p → ℝ) (hlamStar : ∀ i, 0 ≤ lamStar i)
    (hstationarity :
      -((∇ f xstar) + (∑ i, lamStar i • ∇ (g i) xstar) + (∑ j, yStar j • w j)) ∈
        normalCone X xstar)
    (hcomplementary : ∀ i, lamStar i * g i xstar = 0) :
    ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x := by
  intro x hx hgx hhx
  have hf := af191e75_grad_ineq hfconv hxstar hx hfdiff
  have hgi : ∀ i, lamStar i * inner ℝ (∇ (g i) xstar) (x - xstar) ≤ 0 := by
    intro i
    have := af191e75_grad_ineq (hgconv i) hxstar hx (hgdiff i)
    have h2 : inner ℝ (∇ (g i) xstar) (x - xstar) ≤ g i x - g i xstar := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (hlamStar i)
    have h4 := mul_nonpos_of_nonneg_of_nonpos (hlamStar i) (hgx i)
    nlinarith [hcomplementary i]
  have hwj : ∀ j, inner ℝ (w j) (x - xstar) = 0 := by
    intro j
    have a := hh j x
    have c := hh j xstar
    rw [inner_sub_right]
    linarith [hhx j, hxstar_h j]
  have hst := hstationarity x hx
  simp only [inner_neg_left, inner_add_left, sum_inner, inner_smul_left] at hst
  simp only [RCLike.conj_to_real, hwj, mul_zero, Finset.sum_const_zero, add_zero] at hst
  have hsum : ∑ i, lamStar i * inner ℝ (∇ (g i) xstar) (x - xstar) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => hgi i)
  linarith
