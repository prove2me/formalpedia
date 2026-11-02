-- Prove2me | solution 1 for FiniteEnergyPlane.mul_im_conj_pos_of_eigenEq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T21:53:32.152197+00:00
-- url     : https://prove2.me/submissions/396b9e21-e9f0-4259-b8c8-89cdd91ee5de

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasDerivAt_im_conj_mul_of_eigenEq
import Theorems.Thm_FiniteEnergyPlane_pos_of_hasDerivAt_pos_of_eq_zero
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue



namespace FiniteEnergyPlane

theorem mul_im_conj_pos_of_eigenEq_aux (S : ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ t, (S t).IsSymm) {μ ν : ℝ} (hμν : μ ≠ ν) {e f x : ℝ → CauchyRiemannIndex.Vec 1}
    (he : Differentiable ℝ e)
    (hee : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv e t)) -
      Matrix.toEuclideanLin (S t) (e t) = μ • e t)
    (hf : Differentiable ℝ f)
    (hfe : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv f t)) -
      Matrix.toEuclideanLin (S t) (f t) = ν • f t)
    (hx : Differentiable ℝ x)
    (hxe : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv x t)) -
      Matrix.toEuclideanLin (S t) (x t) = ν • x t)
    (hx0 : x 0 = e 0)
    (hfe0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (starRingEnd ℂ (vecToC (f t)) * vecToC (e t)).im ≠ 0) :
    0 < (ν - μ) * (starRingEnd ℂ (vecToC (e 1)) * vecToC (x 1)).im := by
  set P : ℝ → ℝ := fun t => (starRingEnd ℂ (vecToC (f t)) * vecToC (e t)).im with hP
  set W : ℝ → ℝ := fun t => (starRingEnd ℂ (vecToC (f t)) * vecToC (x t)).im with hW
  set Q : ℝ → ℝ := fun t => (starRingEnd ℂ (vecToC (e t)) * vecToC (x t)).im with hQ
  set R : ℝ → ℝ := fun t => (starRingEnd ℂ (vecToC (e t)) * vecToC (x t)).re with hR
  -- `W` is constant, equal to `P 0`
  have hWd : ∀ t, HasDerivAt W ((ν - ν) * (starRingEnd ℂ (vecToC (f t)) * vecToC (x t)).re) t :=
    hasDerivAt_im_conj_mul_of_eigenEq S hS hf hfe hx hxe
  have hWc : ∀ t, W t = P 0 := by
    intro t
    have h := is_const_of_deriv_eq_zero (fun s => (hWd s).differentiableAt)
      (fun s => by rw [(hWd s).deriv]; ring) t 0
    rw [h]
    simp only [hW, hP, hx0]
  -- `P` keeps the sign of `P 0` on `[0, 1]`
  have hPd : ∀ t, HasDerivAt P ((μ - ν) * (starRingEnd ℂ (vecToC (f t)) * vecToC (e t)).re) t :=
    hasDerivAt_im_conj_mul_of_eigenEq S hS hf hfe he hee
  have hPcont : Continuous P := continuous_iff_continuousAt.2 fun t => (hPd t).continuousAt
  have hPsign : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < P t * P 0 := by
    intro t ht
    by_contra hn
    push_neg at hn
    have h0mem : (0 : ℝ) ∈ Set.uIcc (P 0) (P t) := by
      rcases le_total (P 0) 0 with h1 | h1
      · have : 0 ≤ P t := by
          by_contra h2
          push_neg at h2
          have := hfe0 0 ⟨le_refl 0, zero_le_one⟩
          nlinarith [lt_of_le_of_ne h1 this]
        exact Set.mem_uIcc.2 (Or.inl ⟨h1, this⟩)
      · have : P t ≤ 0 := by
          by_contra h2
          push_neg at h2
          have := hfe0 0 ⟨le_refl 0, zero_le_one⟩
          nlinarith [lt_of_le_of_ne h1 (Ne.symm this)]
        exact Set.mem_uIcc.2 (Or.inr ⟨this, h1⟩)
    obtain ⟨s, hs, hPs⟩ := intermediate_value_uIcc hPcont.continuousOn h0mem
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    exact hfe0 s hs' hPs
  -- algebraic identity in `ℂ`
  have alg : ∀ a b z : ℂ, (starRingEnd ℂ b * a).im * (starRingEnd ℂ a * z).re +
      (starRingEnd ℂ a * z).im * (starRingEnd ℂ b * a).re =
      (starRingEnd ℂ b * z).im * Complex.normSq a := by
    intro a b z
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  -- the derivative of `(ν - μ) Q` is positive at its zeros in `[0, 1]`
  have hQd : ∀ t, HasDerivAt (fun s => (ν - μ) * Q s) ((ν - μ) * ((ν - μ) * R t)) t :=
    fun t => (hasDerivAt_im_conj_mul_of_eigenEq S hS he hee hx hxe t).const_mul (ν - μ)
  have hsub : ν - μ ≠ 0 := sub_ne_zero.2 (Ne.symm hμν)
  refine pos_of_hasDerivAt_pos_of_eq_zero (f := fun s => (ν - μ) * Q s) zero_lt_one
    (fun t _ => hQd t) ?_ ?_
  · simp only [hQ, hx0]
    have : (starRingEnd ℂ (vecToC (e 0)) * vecToC (e 0)).im = 0 := by
      simp [Complex.mul_im]; ring
    rw [this, mul_zero]
  · intro t ht hzero
    have hQt : Q t = 0 := (mul_eq_zero.1 hzero).resolve_left hsub
    have hid := alg (vecToC (e t)) (vecToC (f t)) (vecToC (x t))
    have hPt : P t * R t = P 0 * Complex.normSq (vecToC (e t)) := by
      have h1 : W t = P 0 := hWc t
      simp only [hP, hR, hW, hQ] at hid h1 hQt ⊢
      rw [hQt, zero_mul, add_zero, h1] at hid
      exact hid
    have hen : vecToC (e t) ≠ 0 := by
      intro h0
      apply hfe0 t ht
      rw [h0, mul_zero, Complex.zero_im]
    have hns : 0 < Complex.normSq (vecToC (e t)) := Complex.normSq_pos.2 hen
    have hs := hPsign t ht
    have hP0 : P 0 ≠ 0 := hfe0 0 ⟨le_refl 0, zero_le_one⟩
    have hRpos : 0 < R t := by
      have h2 : P t * P 0 * R t = P 0 ^ 2 * Complex.normSq (vecToC (e t)) := by
        rw [mul_right_comm, hPt]; ring
      have h3 : 0 < P 0 ^ 2 * Complex.normSq (vecToC (e t)) := by positivity
      rw [← h2] at h3
      exact pos_of_mul_pos_right h3 hs.le
    have : 0 < (ν - μ) * (ν - μ) := mul_self_pos.2 hsub
    show 0 < (ν - μ) * ((ν - μ) * R t)
    rw [← mul_assoc]
    positivity

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (S : ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ t, (S t).IsSymm) {μ ν : ℝ} (hμν : μ ≠ ν) {e f x : ℝ → CauchyRiemannIndex.Vec 1}
    (he : Differentiable ℝ e)
    (hee : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv e t)) -
      Matrix.toEuclideanLin (S t) (e t) = μ • e t)
    (hf : Differentiable ℝ f)
    (hfe : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv f t)) -
      Matrix.toEuclideanLin (S t) (f t) = ν • f t)
    (hx : Differentiable ℝ x)
    (hxe : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv x t)) -
      Matrix.toEuclideanLin (S t) (x t) = ν • x t)
    (hx0 : x 0 = e 0)
    (hfe0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (starRingEnd ℂ (vecToC (f t)) * vecToC (e t)).im ≠ 0) :
    0 < (ν - μ) * (starRingEnd ℂ (vecToC (e 1)) * vecToC (x 1)).im :=
  mul_im_conj_pos_of_eigenEq_aux S hS hμν he hee hf hfe hx hxe hx0 hfe0
