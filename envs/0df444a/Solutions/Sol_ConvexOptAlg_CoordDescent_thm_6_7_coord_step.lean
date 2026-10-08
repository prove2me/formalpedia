-- Prove2me | solution 1 for ConvexOptAlg.CoordDescent.thm_6_7_coord_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:30:22.212933+00:00
-- url     : https://prove2.me/submissions/4bb0e555-6065-4388-8a00-510edf31b02c

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

set_option autoImplicit false

namespace P2e435a24

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

end P2e435a24

open ConvexOptAlg.CoordDescent in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
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
  have key := P2e435a24.descent1d (fun t : ℝ => f (x + t • e)) (fun t => g (x + t • e) i) hd
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
