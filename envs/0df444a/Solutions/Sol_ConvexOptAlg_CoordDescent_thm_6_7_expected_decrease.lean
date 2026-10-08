-- Prove2me | solution 1 for ConvexOptAlg.CoordDescent.thm_6_7_expected_decrease
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:17:59.351131+00:00
-- url     : https://prove2.me/submissions/947a711a-66e5-4f2a-8941-61a8e078aec3

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

set_option autoImplicit false

namespace Pc7278975

lemma descent1d (φ φ' : ℝ → ℝ) (hd : ∀ t, HasDerivAt φ (φ' t) t) (b : ℝ)
    (hb : ∀ t, |φ' t - φ' 0| ≤ b * |t|) (u : ℝ) :
    φ u - φ 0 ≤ u * φ' 0 + b / 2 * u ^ 2 := by
  set h : ℝ → ℝ := fun t => φ t - t * φ' 0 - b / 2 * t ^ 2 with hh
  have hhd : ∀ t, HasDerivAt h (φ' t - φ' 0 - b * t) t := by
    intro t
    have h1 := ((hd t).sub ((hasDerivAt_id t).mul_const (φ' 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (b / 2))
    convert h1 using 1 <;> first | rfl | ring1 | (simp; rfl) | (simp; ring1) | (simp [id]; ring1)
  have hcont : Continuous h := continuous_iff_continuousAt.2 fun t => (hhd t).continuousAt
  have key : h u ≤ h 0 := by
    rcases le_or_gt 0 u with hu | hu
    · have hanti : AntitoneOn h (Set.Ici 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn
        · intro t _; exact (hhd t).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [interior_Ici] at ht
          rw [(hhd t).deriv]
          have := hb t
          rw [abs_of_pos (Set.mem_Ioi.1 ht)] at this
          have := (abs_le.1 this).2
          linarith
      exact hanti (Set.mem_Ici.2 le_rfl) hu hu
    · have hmono : MonotoneOn h (Set.Iic 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Iic 0) hcont.continuousOn
        · intro t _; exact (hhd t).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [interior_Iic] at ht
          rw [(hhd t).deriv]
          have := hb t
          rw [abs_of_neg (Set.mem_Iio.1 ht)] at this
          have := (abs_le.1 this).1
          nlinarith
      exact hmono (le_of_lt hu) (Set.mem_Iic.2 le_rfl) (le_of_lt hu)
  simp only [hh] at key
  nlinarith [key]

open ConvexOptAlg.CoordDescent in
lemma stepDec {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ)
    (hsm : IsCoordSmooth f g β) (i : Fin n) (hβi : 0 < β i) (x : EuclideanSpace ℝ (Fin n)) :
    f (rcdStep β g x i) - f x ≤ -(1 / (2 * β i)) * g x i ^ 2 := by
  obtain ⟨hg, hs⟩ := hsm
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1 with he
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • e)) (g (x + t • e) i) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add x
    have h2 := (hg (x + t • e)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (g (x + t • e))) e
        = g (x + t • e) i := by
      rw [InnerProductSpace.toDual_apply_apply, he, EuclideanSpace.inner_single_right]
      simp
    exact h2.congr_deriv h3
  have hb : ∀ t : ℝ, |g (x + t • e) i - g (x + (0:ℝ) • e) i| ≤ β i * |t| := by
    intro t
    simpa using hs i x t
  have key := descent1d (fun t : ℝ => f (x + t • e)) (fun t => g (x + t • e) i) hd
    (β i) hb (-(1 / β i * g x i))
  simp only [zero_smul, add_zero] at key
  have hstep : rcdStep β g x i = x + (-(1 / β i * g x i)) • e := by
    simp only [rcdStep, he, neg_smul, sub_eq_add_neg]
  rw [hstep]
  have hne : β i ≠ 0 := ne_of_gt hβi
  have : -(1 / β i * g x i) * g x i + β i / 2 * (-(1 / β i * g x i)) ^ 2
      = -(1 / (2 * β i)) * g x i ^ 2 := by
    field_simp; ring
  linarith

end Pc7278975

open ConvexOptAlg.CoordDescent in
theorem solution {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ) (γ : ℝ)
    (hγ : 0 ≤ γ) (hβ : ∀ i, 0 < β i) (hsm : IsCoordSmooth f g β) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, pGamma β γ i * f (rcdStep β g x i)) - f x ≤
      -(1 / (2 * ∑ i, β i ^ γ)) * wnormDual β (1 - γ) (g x) ^ 2 := by
  have hpos : ∀ i, 0 < β i ^ γ := fun i => Real.rpow_pos_of_pos (hβ i) γ
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hS : 0 < ∑ i, β i ^ γ := Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  have hsum1 : ∑ i, pGamma β γ i = 1 := by
    simp only [pGamma, ← Finset.sum_div]
    exact div_self (ne_of_gt hS)
  have hw : wnormDual β (1 - γ) (g x) ^ 2 = ∑ i, g x i ^ 2 / β i ^ (1 - γ) := by
    unfold wnormDual
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ =>
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (hβ i)) _)
  rw [hw]
  have hlhs : (∑ i, pGamma β γ i * f (rcdStep β g x i)) - f x
      = ∑ i, pGamma β γ i * (f (rcdStep β g x i) - f x) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul]
  rw [hlhs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hp : 0 ≤ pGamma β γ i := div_nonneg (le_of_lt (hpos i)) (le_of_lt hS)
  have hd := Pc7278975.stepDec f g β hsm i (hβ i) x
  have h1 : pGamma β γ i * (f (rcdStep β g x i) - f x)
      ≤ pGamma β γ i * (-(1 / (2 * β i)) * g x i ^ 2) := mul_le_mul_of_nonneg_left hd hp
  have hr : β i ^ (1 - γ) = β i / β i ^ γ := by
    rw [Real.rpow_sub (hβ i), Real.rpow_one]
  have h2 : pGamma β γ i * (-(1 / (2 * β i)) * g x i ^ 2)
      = -(1 / (2 * ∑ j, β j ^ γ)) * (g x i ^ 2 / β i ^ (1 - γ)) := by
    rw [hr]
    unfold pGamma
    have := ne_of_gt (hβ i)
    have := ne_of_gt (hpos i)
    have := ne_of_gt hS
    field_simp
  linarith
