-- Prove2me | solution 1 for DynSampleSize.Det.eq_4_6
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T10:33:33.919809+00:00
-- url     : https://prove2.me/submissions/46bd2a4d-4abc-44c7-ab88-bbb9dea8dbb7

import Mathlib
import Definitions.Def_DynSampleSize_Det_Setting
namespace AcceptedGap

set_option autoImplicit false
open DynSampleSize.Det



lemma dss_oneD (φ g h : ℝ → ℝ) (c : ℝ) (hφ : ∀ t, HasDerivAt φ (g t) t)
    (hg : ∀ t, HasDerivAt g (h t) t) (hh : ∀ t, h t ≤ c) : φ 1 ≤ φ 0 + g 0 + c / 2 := by
  have hgt : ∀ t, 0 ≤ t → g t ≤ g 0 + c * t := by
    intro t ht
    have hF : ∀ x, HasDerivAt (fun x => g x - c * x) (h x - c) x := fun x =>
      ((hg x).sub ((hasDerivAt_id' x).const_mul c)).congr_deriv (by ring)
    have hanti : Antitone (fun x => g x - c * x) :=
      antitone_of_deriv_nonpos (fun x => (hF x).differentiableAt) (fun x => by
        rw [(hF x).deriv]; linarith [hh x])
    have := hanti ht
    simp only [mul_zero, sub_zero] at this
    linarith
  have hF : ∀ x, HasDerivAt (fun x => φ x - g 0 * x - c / 2 * x ^ 2) (g x - g 0 - c * x) x := by
    intro x
    have h1 := (hφ x).sub ((hasDerivAt_id' x).const_mul (g 0))
    have h2 := ((hasDerivAt_pow 2 x).const_mul (c / 2))
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    norm_num <;> ring
  have hanti : AntitoneOn (fun x => φ x - g 0 * x - c / 2 * x ^ 2) (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun x _ => (hF x).continuousAt.continuousWithinAt
    · exact fun x _ => (hF x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hF x).deriv]
      linarith [hgt x hx.1.le]
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [mul_zero, sub_zero, zero_pow two_ne_zero, mul_one, one_pow] at this
  linarith

lemma dss_quad {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (w d : EuclideanSpace ℝ (Fin m)) :
    J w + inner ℝ (gradient J w) d + lam / 2 * ‖d‖ ^ 2 ≤ J (w + d) ∧
      J (w + d) ≤ J w + inner ℝ (gradient J w) d + L / 2 * ‖d‖ ^ 2 := by
  obtain ⟨hC, -, -, hH⟩ := hJ
  have hdiff : Differentiable ℝ J := hC.differentiable (by norm_num)
  have hdiff2 : Differentiable ℝ (fderiv ℝ J) :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set γ : ℝ → EuclideanSpace ℝ (Fin m) := fun t => w + t • d with hγ
  have hγd : ∀ t, HasDerivAt γ d t := fun t => by
    simpa [hγ] using ((hasDerivAt_id' t).smul_const d).const_add w
  have h1 : ∀ t, HasDerivAt (fun t => J (γ t)) (fderiv ℝ J (γ t) d) t := fun t =>
    (hdiff (γ t)).hasFDerivAt.comp_hasDerivAt t (hγd t)
  have h2 : ∀ t, HasDerivAt (fun t => fderiv ℝ J (γ t) d)
      (fderiv ℝ (fderiv ℝ J) (γ t) d d) t := fun t => by
    have := (hdiff2 (γ t)).hasFDerivAt.comp_hasDerivAt t (hγd t)
    exact (ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp_hasDerivAt t this
  have hgrad : fderiv ℝ J w d = inner ℝ (gradient J w) d := by
    unfold gradient
    rw [InnerProductSpace.toDual_symm_apply]
  have e0 : γ 0 = w := by simp [hγ]
  have e1 : γ 1 = w + d := by simp [hγ]
  constructor
  · have := dss_oneD (fun t => -J (γ t)) (fun t => -fderiv ℝ J (γ t) d)
      (fun t => -fderiv ℝ (fderiv ℝ J) (γ t) d d) (-(lam * ‖d‖ ^ 2))
      (fun t => (h1 t).neg) (fun t => (h2 t).neg) (fun t => by linarith [(hH (γ t) d).1])
    simp only [e0, e1, hgrad] at this
    linarith
  · have := dss_oneD (fun t => J (γ t)) (fun t => fderiv ℝ J (γ t) d)
      (fun t => fderiv ℝ (fderiv ℝ J) (γ t) d d) (L * ‖d‖ ^ 2)
      h1 h2 (fun t => (hH (γ t) d).2)
    simp only [e0, e1, hgrad] at this
    linarith

lemma dss_taylor {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (w g : EuclideanSpace ℝ (Fin m)) :
    J (w - (1 / L) • g) ≤ J w - (1 / L) * inner ℝ (gradient J w) g + 1 / (2 * L) * ‖g‖ ^ 2 := by
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have := (dss_quad J lam L hJ w ((-(1 / L)) • g)).2
  have e : w + (-(1 / L)) • g = w - (1 / L) • g := by rw [neg_smul, sub_eq_add_neg]
  rw [e, inner_smul_right, norm_smul, mul_pow] at this
  have h2 : ‖-(1 / L)‖ ^ 2 = (1 / L) ^ 2 := by
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
  rw [h2] at this
  have h3 : L / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) = 1 / (2 * L) * ‖g‖ ^ 2 := by
    field_simp
  rw [h3] at this
  linarith

lemma dss_lower {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (w g : EuclideanSpace ℝ (Fin m)) :
    J w - (1 / L) * (‖gradient J w‖ * ‖g‖) ≤ J (w - (1 / L) • g) := by
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have hlam : 0 < lam := hJ.2.1
  have := (dss_quad J lam L hJ w ((-(1 / L)) • g)).1
  have e : w + (-(1 / L)) • g = w - (1 / L) • g := by rw [neg_smul, sub_eq_add_neg]
  rw [e, inner_smul_right] at this
  have h1 : inner ℝ (gradient J w) g ≤ ‖gradient J w‖ * ‖g‖ := by
    have := abs_real_inner_le_norm (gradient J w) g
    linarith [le_abs_self (inner ℝ (gradient J w) g)]
  have h2 : 0 ≤ lam / 2 * ‖(-(1 / L)) • g‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 / L by positivity)]


lemma dss_gd {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hwstar : ∀ w, J wstar ≤ J w) (w : EuclideanSpace ℝ (Fin m)) :
    lam * (J w - J wstar) ≤ inner ℝ (gradient J w) (gradient J w) := by
  have hlam : 0 < lam := hJ.2.1
  have h := (dss_quad J lam L hJ w (wstar - w)).1
  rw [add_sub_cancel] at h
  have h1 := hwstar w
  have h2 : -(‖gradient J w‖ * ‖wstar - w‖) ≤ inner ℝ (gradient J w) (wstar - w) := by
    have := abs_real_inner_le_norm (gradient J w) (wstar - w)
    linarith [neg_abs_le (inner ℝ (gradient J w) (wstar - w))]
  rw [real_inner_self_eq_norm_sq]
  set G := ‖gradient J w‖
  set r := ‖wstar - w‖
  have h3 : J w - J wstar ≤ G * r - lam / 2 * r ^ 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hlam.le, sq_nonneg (G - lam * r), sq_nonneg G]


theorem solution {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hwstar : ∀ w, J wstar ≤ J w) (w : EuclideanSpace ℝ (Fin m)) :
    lam * (J w - J wstar) ≤ inner ℝ (gradient J w) (gradient J w) :=
  dss_gd J lam L hJ wstar hwstar w
end AcceptedGap
open DynSampleSize.Det

theorem solution {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hmin : ∀ w, J wstar ≤ J w) (w : EuclideanSpace ℝ (Fin m)) :
    lam / (2 * L ^ 2) * ‖gradient J w‖ ^ 2 ≤ J w - J wstar  := by
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have ht := AcceptedGap.dss_taylor J lam L hJ w (gradient J w)
  rw [real_inner_self_eq_norm_sq] at ht
  have hm := hmin (w - (1/L) • gradient J w)
  have he : (1:ℝ)/L = 2*(1/(2*L)) := by field_simp
  have hg : 1/(2*L)*‖gradient J w‖^2 ≤ J w-J wstar := by rw [he] at ht hm; linarith
  have hc : lam/(2*L^2) ≤ 1/(2*L) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_pos hL (sub_pos.mpr hJ.2.2.1)]
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans hg



#print axioms solution
