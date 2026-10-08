-- Prove2me | solution 1 for ConvexOptAlg.CoordDescent.thm_6_8_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:48:14.541488+00:00
-- url     : https://prove2.me/submissions/6ce2e2bf-2310-4671-8d98-35600fc7638e

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

set_option autoImplicit false

namespace Pd265d9f8

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

lemma coord_bound (g d α w : ℝ) (hα : 0 < α) (hw : 0 < w) :
    g * d - α / 2 * (w * d ^ 2) ≤ g ^ 2 / (2 * α * w) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (g - α * w * d), mul_pos hα hw]

end Pd265d9f8

open ConvexOptAlg.CoordDescent in
theorem solution {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ) (γ α : ℝ)
    (hγ : 0 ≤ γ) (hβ : ∀ i, 0 < β i) (hα : 0 < α)
    (hsc : IsStronglyConvexWNorm f g β (1 - γ) α) (hsm : IsCoordSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, pGamma β γ i * f (rcdStep β g x i)) - f xstar ≤
      (1 - 1 / kappa β γ α) * (f x - f xstar) := by
  obtain ⟨_, hsc2⟩ := hsc
  set S := ∑ j, β j ^ γ with hS
  have hb : ∀ i, 0 < β i ^ γ := fun i => Real.rpow_pos_of_pos (hβ i) γ
  have hw : ∀ i, 0 < β i ^ (1 - γ) := fun i => Real.rpow_pos_of_pos (hβ i) _
  have hwb : ∀ i, β i ^ (1 - γ) * β i ^ γ = β i := by
    intro i; rw [← Real.rpow_add (hβ i)]; simp
  have hSpos : 0 < S := Finset.sum_pos (fun i _ => hb i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hp1 : ∑ i, pGamma β γ i = 1 := by
    simp only [pGamma]; rw [← Finset.sum_div]; exact div_self hSpos.ne'
  have hp0 : ∀ i, 0 ≤ pGamma β γ i := fun i => div_nonneg (hb i).le hSpos.le
  set Q := ∑ i, β i ^ γ * g x i ^ 2 / (2 * β i) with hQ
  -- expected decrease
  have hdec : (∑ i, pGamma β γ i * f (rcdStep β g x i)) ≤ f x - Q / S := by
    have h1 : (∑ i, pGamma β γ i * f (rcdStep β g x i)) ≤
        ∑ i, (pGamma β γ i * f x - pGamma β γ i * (1 / (2 * β i) * g x i ^ 2)) := by
      apply Finset.sum_le_sum
      intro i _
      have := Pd265d9f8.stepDec f g β hsm i (hβ i) x
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left (by linarith) (hp0 i)
    have h2 : ∑ i, pGamma β γ i * (1 / (2 * β i) * g x i ^ 2) = Q / S := by
      rw [hQ, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have := (hβ i).ne'
      have hSne := hSpos.ne'
      simp only [pGamma, ← hS]
      field_simp
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, h2, one_mul] at h1
    exact h1
  -- strong convexity bound
  have hscb : f x - f xstar ≤ Q / α := by
    have h := hsc2 x xstar
    have hwn : wnorm β (1 - γ) (x - xstar) ^ 2 = ∑ i, β i ^ (1 - γ) * (x i - xstar i) ^ 2 := by
      unfold wnorm
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (sq_nonneg _)))]
      simp [PiLp.sub_apply]
    rw [hwn, Finset.mul_sum, ← Finset.sum_sub_distrib] at h
    refine h.trans ?_
    rw [hQ, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    refine (Pd265d9f8.coord_bound (g x i) (x i - xstar i) α (β i ^ (1 - γ)) hα (hw i)).trans
      (le_of_eq ?_)
    have h1 := hwb i
    have h2 := (hw i).ne'
    have h3 := (hβ i).ne'
    rw [show (2 * β i) = 2 * (β i ^ (1 - γ) * β i ^ γ) from by rw [h1]]
    have h4 := (hb i).ne'
    field_simp
  have hD : α * (f x - f xstar) ≤ Q := by
    have := mul_le_mul_of_nonneg_left hscb hα.le
    rwa [mul_div_cancel₀ _ hα.ne'] at this
  have hD2 : α * (f x - f xstar) / S ≤ Q / S := div_le_div_of_nonneg_right hD hSpos.le
  have hk : 1 / kappa β γ α = α / S := by
    unfold kappa; rw [one_div_div]
  rw [hk]
  have : (1 - α / S) * (f x - f xstar) = (f x - f xstar) - α * (f x - f xstar) / S := by ring
  rw [this]
  linarith
