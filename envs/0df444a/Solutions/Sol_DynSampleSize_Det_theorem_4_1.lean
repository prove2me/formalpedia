-- Prove2me | solution 1 for DynSampleSize.Det.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T10:39:11.541124+00:00
-- url     : https://prove2.me/submissions/f645c6de-663d-43e2-b3bb-323144647ac5

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


theorem gradient_gap {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hwstar : ∀ w, J wstar ≤ J w) (w : EuclideanSpace ℝ (Fin m)) :
    lam * (J w - J wstar) ≤ inner ℝ (gradient J w) (gradient J w) :=
  dss_gd J lam L hJ wstar hwstar w
end AcceptedGap
open DynSampleSize.Det

theorem gradient_gap {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
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



#print axioms gradient_gap

namespace AcceptedDescent
set_option autoImplicit false
open Filter Topology
open DynSampleSize.Det

theorem solution {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (g w : ℕ → EuclideanSpace ℝ (Fin m))
    (hw : ∀ k, w (k + 1) = w k - ((1 - θ) / L) • g k) (k : ℕ)
    (h48 : ‖g k - gradient J (w k)‖ ≤ θ * ‖g k‖) :
    J (w (k + 1)) ≤ J (w k) - beta θ / L * ‖gradient J (w k)‖ ^ 2 := by
  obtain ⟨hC, hlam, hlamL, hess⟩ := hJ
  have hL : 0 < L := lt_trans hlam hlamL
  have descent : ∀ x s : EuclideanSpace ℝ (Fin m),
      J (x + s) ≤ J x + fderiv ℝ J x s + L / 2 * ‖s‖ ^ 2 := by
    intro x s
    have hJd : Differentiable ℝ J := hC.differentiable (by norm_num)
    have hf1 : Differentiable ℝ (fderiv ℝ J) :=
      (hC.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    set c : ℝ := L * ‖s‖ ^ 2 with hc
    let γ : ℝ → EuclideanSpace ℝ (Fin m) := fun t => x + t • s
    have hγ : ∀ t, HasDerivAt γ s t := fun t => by
      exact (((hasDerivAt_id t).smul_const s).const_add x).congr_deriv (one_smul ℝ s)
    have hφ : ∀ t, HasDerivAt (fun t => J (γ t)) (fderiv ℝ J (γ t) s) t := fun t =>
      (hJd (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
    have hφ' : ∀ t, HasDerivAt (fun t => fderiv ℝ J (γ t) s)
        (fderiv ℝ (fderiv ℝ J) (γ t) s s) t := by
      intro t
      have h1 : HasDerivAt (fun t => fderiv ℝ J (γ t)) (fderiv ℝ (fderiv ℝ J) (γ t) s) t :=
        (hf1 (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
      simpa using h1.clm_apply (hasDerivAt_const t s)
    let ψ : ℝ → ℝ := fun t => J x + fderiv ℝ J x s * t + c * t ^ 2 / 2 - J (γ t)
    let ψ' : ℝ → ℝ := fun t => fderiv ℝ J x s + c * t - fderiv ℝ J (γ t) s
    have hψ : ∀ t, HasDerivAt ψ (ψ' t) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => J x + fderiv ℝ J x s * t + c * t ^ 2 / 2)
          (fderiv ℝ J x s + c * t) t := by
        have := ((hasDerivAt_id t).const_mul (fderiv ℝ J x s)).const_add (J x)
        have h2 := (((hasDerivAt_id t).pow 2).const_mul c).div_const 2
        have key := this.add h2
        exact key.congr_deriv (by first | (simp; ring) | simp | ring | (norm_num; ring))
      exact h1.sub (hφ t)
    have hψ' : ∀ t, HasDerivAt ψ' (c - fderiv ℝ (fderiv ℝ J) (γ t) s s) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ J x s + c * t) c t := by
        simpa using ((hasDerivAt_id t).const_mul c).const_add (fderiv ℝ J x s)
      exact h1.sub (hφ' t)
    have hmono' : Monotone ψ' := by
      apply monotone_of_deriv_nonneg (fun t => (hψ' t).differentiableAt)
      intro t
      rw [(hψ' t).deriv]
      have := (hess (γ t) s).2
      rw [hc]; linarith
    have hψ'0 : ψ' 0 = 0 := by simp [ψ', γ]
    have hmonoψ : MonotoneOn ψ (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun t _ => (hψ t).continuousAt.continuousWithinAt
      · exact fun t _ => (hψ t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hψ t).deriv]
        have := hmono' (le_of_lt (Set.mem_Ioi.1 ht))
        linarith
    have h01 := hmonoψ (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
    simp only [ψ, γ] at h01
    simp only [zero_smul, add_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_div, sub_self, one_smul, mul_one, one_pow] at h01
    rw [hc] at h01
    linarith
  set v := gradient J (w k) with hv
  have hinner : ∀ s, inner ℝ v s = fderiv ℝ J (w k) s := by
    intro s
    simp [hv, gradient]
  have hn : ‖g k‖ ≥ 0 := norm_nonneg _
  have e1 : (1 - θ) * ‖g k‖ ^ 2 ≤ inner ℝ v (g k) := by
    have h1 : inner ℝ (g k - v) (g k) ≤ ‖g k - v‖ * ‖g k‖ := real_inner_le_norm _ _
    have h2 : inner ℝ (g k - v) (g k) = ‖g k‖ ^ 2 - inner ℝ v (g k) := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have h3 : ‖g k - v‖ * ‖g k‖ ≤ θ * ‖g k‖ * ‖g k‖ :=
      mul_le_mul_of_nonneg_right h48 (norm_nonneg _)
    nlinarith [h1, h2, h3]
  have e2 : ‖v‖ ≤ (1 + θ) * ‖g k‖ := by
    have h := abs_norm_sub_norm_le (g k) v
    have h' := abs_le.mp (h.trans h48)
    linarith [h'.1, h'.2]
  have hstep := descent (w k) (-(((1 - θ) / L) • g k))
  have e3 : w (k + 1) = w k + -(((1 - θ) / L) • g k) := by rw [hw k]; abel
  rw [e3]
  have e4 : fderiv ℝ J (w k) (-(((1 - θ) / L) • g k)) = -((1 - θ) / L) * inner ℝ v (g k) := by
    rw [← hinner]
    simp [inner_neg_right, inner_smul_right]
  have e5 : ‖-(((1 - θ) / L) • g k)‖ ^ 2 = ((1 - θ) / L) ^ 2 * ‖g k‖ ^ 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [e4, e5] at hstep
  have hβ : beta θ = (1 - θ) ^ 2 / (2 * (1 + θ) ^ 2) := rfl
  have e6 : ‖v‖ ^ 2 ≤ (1 + θ) ^ 2 * ‖g k‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) e2 2
  have h1θ : 0 < 1 - θ := by linarith
  have hθp : 0 < (1 + θ) ^ 2 := by positivity
  have e7 : beta θ / L * ‖v‖ ^ 2 ≤ (1 - θ) ^ 2 / (2 * L) * ‖g k‖ ^ 2 := by
    rw [hβ]
    have : (1 - θ) ^ 2 / (2 * (1 + θ) ^ 2) / L * ‖v‖ ^ 2 ≤
        (1 - θ) ^ 2 / (2 * (1 + θ) ^ 2) / L * ((1 + θ) ^ 2 * ‖g k‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left e6
      positivity
    refine this.trans (le_of_eq ?_)
    field_simp
  have e8 : -((1 - θ) / L) * inner ℝ v (g k) ≤ -((1 - θ) / L) * ((1 - θ) * ‖g k‖ ^ 2) := by
    have : 0 ≤ (1 - θ) / L := by positivity
    nlinarith [e1]
  have e9 : L / 2 * (((1 - θ) / L) ^ 2 * ‖g k‖ ^ 2) = (1 - θ) ^ 2 / (2 * L) * ‖g k‖ ^ 2 := by
    field_simp
  have e10 : -((1 - θ) / L) * ((1 - θ) * ‖g k‖ ^ 2) = -((1 - θ) ^ 2 / L * ‖g k‖ ^ 2) := by
    field_simp
  have e11 : (1 - θ) ^ 2 / L * ‖g k‖ ^ 2 = 2 * ((1 - θ) ^ 2 / (2 * L) * ‖g k‖ ^ 2) := by
    field_simp
  linarith
end AcceptedDescent

open DynSampleSize.Det Filter Topology
namespace DynamicConvergence

lemma beta_range (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) : 0 < beta θ ∧ beta θ < 1 := by
  have ht : 0 < 1-θ := by linarith
  constructor
  · unfold beta; positivity
  · unfold beta
    apply (div_lt_one (by positivity : 0 < 2*(1+θ)^2)).mpr
    nlinarith [sq_nonneg θ]

lemma rate_range (lam L θ : ℝ) (hlam : 0 < lam) (hlamL : lam < L)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    0 < beta θ * lam / L ∧ beta θ * lam / L < 1 := by
  have hL : 0 < L := hlam.trans hlamL
  obtain ⟨hb,hb1⟩ := beta_range θ hθ0 hθ1
  constructor
  · positivity
  · apply (div_lt_one hL).mpr
    nlinarith [mul_pos hlam (sub_pos.mpr hb1)]

lemma one_step {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hmin : ∀ w, J wstar ≤ J w) (hJstar : J wstar = 0)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (g w : ℕ → EuclideanSpace ℝ (Fin m))
    (hw : ∀ k, w (k+1) = w k-((1-θ)/L) • g k) (k : ℕ)
    (ha : ‖g k-gradient J (w k)‖ ≤ θ*‖g k‖) :
    J (w (k+1)) ≤ (1-beta θ*lam/L)*J (w k) := by
  have hd := AcceptedDescent.solution J lam L hJ θ hθ0 hθ1 g w hw k ha
  have hg := AcceptedGap.dss_gd J lam L hJ wstar hmin (w k)
  rw [hJstar,sub_zero,real_inner_self_eq_norm_sq] at hg
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have hb := (beta_range θ hθ0 hθ1).1
  have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ beta θ/L by positivity)
  have he : (1-beta θ*lam/L)*J (w k) = J (w k)-beta θ/L*(lam*J (w k)) := by ring
  rw [he]
  linarith

end DynamicConvergence

theorem geometric_bound {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hmin : ∀ w, J wstar ≤ J w) (hJstar : J wstar = 0)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (g w : ℕ → EuclideanSpace ℝ (Fin m))
    (hw : ∀ k, w (k+1) = w k-((1-θ)/L) • g k) (k : ℕ)
    (h48 : ∀ j < k, ‖g j-gradient J (w j)‖ ≤ θ*‖g j‖) :
    J (w k) ≤ (1-beta θ*lam/L)^k*J (w 0) := by
  have hq : 0 ≤ 1-beta θ*lam/L := by
    have h := (DynamicConvergence.rate_range lam L θ hJ.2.1 hJ.2.2.1 hθ0 hθ1).2
    linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have hp := ih (fun j hj => h48 j (Nat.lt_succ_of_lt hj))
    have hs := DynamicConvergence.one_step J lam L hJ wstar hmin hJstar θ hθ0 hθ1 g w hw k
      (h48 k (Nat.lt_succ_self k))
    calc _ ≤ (1-beta θ*lam/L)*J (w k) := hs
      _ ≤ (1-beta θ*lam/L)*((1-beta θ*lam/L)^k*J (w 0)) := mul_le_mul_of_nonneg_left hp hq
      _ = _ := by rw [pow_succ]; ring

#print axioms geometric_bound

open DynSampleSize.Det Filter Topology

theorem solution {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hmin : ∀ w, J wstar ≤ J w) (hJstar : J wstar = 0)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (g w : ℕ → EuclideanSpace ℝ (Fin m))
    (hw : ∀ k, w (k+1) = w k-((1-θ)/L) • g k) :
    (∀ k, ‖g k-gradient J (w k)‖ ≤ θ*‖g k‖ →
      J (w (k+1)) ≤ (1-beta θ*lam/L)*J (w k)) ∧
    ((∀ k, ‖g k-gradient J (w k)‖ ≤ θ*‖g k‖) →
      Tendsto w atTop (𝓝 wstar) ∧
      (∀ ε : ℝ, 0 < ε → ∀ k : ℕ,
        L/(beta θ*lam)*(Real.log (1/ε)+Real.log (J (w 0))) < (k : ℝ) → J (w k) < ε) ∧
      (∀ k : ℕ, ‖g k‖^2 ≤
        1/(1-θ)^2*(2*L^2*J (w 0)/lam)*(1-beta θ*lam/L)^k)) := by
  have hlam : 0 < lam := hJ.2.1
  have hL : 0 < L := hlam.trans hJ.2.2.1
  have hb := (DynamicConvergence.beta_range θ hθ0 hθ1).1
  have hθ : 0 < 1-θ := by linarith
  let a := beta θ*lam/L
  let q := 1-a
  have ha : 0 < a := (DynamicConvergence.rate_range lam L θ hlam hJ.2.2.1 hθ0 hθ1).1
  have ha1 : a < 1 := (DynamicConvergence.rate_range lam L θ hlam hJ.2.2.1 hθ0 hθ1).2
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hJ0 (x : EuclideanSpace ℝ (Fin m)) : 0 ≤ J x := by simpa [hJstar] using hmin x
  constructor
  · exact DynamicConvergence.one_step J lam L hJ wstar hmin hJstar θ hθ0 hθ1 g w hw
  · intro h48
    have hgeo (k : ℕ) : J (w k) ≤ q^k*J (w 0) :=
      geometric_bound J lam L hJ wstar hmin hJstar θ hθ0 hθ1 g w hw k (fun j _ => h48 j)
    have hgrad0 : gradient J wstar = 0 := by
      have hh := gradient_gap J lam L hJ wstar hmin wstar
      rw [sub_self] at hh
      have hc : 0 < lam/(2*L^2) := by positivity
      apply norm_eq_zero.mp
      by_contra hn
      have hp : 0 < ‖gradient J wstar‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
      have hprod := mul_pos hc (sq_pos_of_pos hp)
      linarith
    have hstrong (x : EuclideanSpace ℝ (Fin m)) : lam/2*‖x-wstar‖^2 ≤ J x := by
      have hh := (AcceptedGap.dss_quad J lam L hJ wstar (x-wstar)).1
      simpa only [hJstar,hgrad0,inner_zero_left,zero_add,add_sub_cancel] using hh
    have hlim : Tendsto (fun k : ℕ => J (w k)) atTop (𝓝 0) := by
      apply squeeze_zero (fun k => hJ0 (w k)) hgeo
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).mul_const (J (w 0))
    refine ⟨?_,?_,?_⟩
    · apply Metric.tendsto_atTop.mpr
      intro ε hε
      have he : 0 < lam/2*ε^2 := by positivity
      have hev := (tendsto_order.mp hlim).2 (lam/2*ε^2) he
      obtain ⟨N,hN⟩ := eventually_atTop.mp hev
      refine ⟨N,fun n hn => ?_⟩
      have hh := hN n hn
      have hl := hstrong (w n)
      rw [dist_eq_norm]
      have hsq : ‖w n-wstar‖^2 < ε^2 :=
        (mul_lt_mul_iff_right₀ (by positivity : 0 < lam/2)).mp (hl.trans_lt hh)
      nlinarith [norm_nonneg (w n-wstar)]
    · intro ε hε k hk
      by_cases hz : J (w 0)=0
      · have hh := hgeo k
        rw [hz,mul_zero] at hh
        exact hh.trans_lt hε
      · have hpos : 0 < J (w 0) := lt_of_le_of_ne (hJ0 _) (Ne.symm hz)
        have heq : L/(beta θ*lam)*(Real.log (1/ε)+Real.log (J (w 0))) =
            (Real.log (1/ε)+Real.log (J (w 0)))/a := by
          dsimp [a]; field_simp
        rw [heq] at hk
        have hk' := (div_lt_iff₀ ha).mp hk
        simp only [one_div,Real.log_inv] at hk'
        have hqe : q ≤ Real.exp (-a) := by
          have hh := Real.add_one_le_exp (-a)
          dsimp [q]; linarith
        have hp := pow_le_pow_left₀ hq0.le hqe k
        have hbound : q^k*J (w 0) ≤ Real.exp (-(k:ℝ)*a)*J (w 0) := by
          have he : Real.exp (-a)^k = Real.exp (-(k:ℝ)*a) := by
            rw [← Real.exp_nat_mul]; congr 1; ring
          rw [he] at hp
          exact mul_le_mul_of_nonneg_right hp hpos.le
        apply (hgeo k).trans_lt
        apply hbound.trans_lt
        calc _ = Real.exp (-(k:ℝ)*a+Real.log (J (w 0))) := by
               rw [Real.exp_add,Real.exp_log hpos]
          _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
          _ = ε := Real.exp_log hε
    · intro k
      have hd := (norm_sub_norm_le (g k) (gradient J (w k))).trans (h48 k)
      have hn : (1-θ)*‖g k‖ ≤ ‖gradient J (w k)‖ := by linarith
      have hn2 : (1-θ)^2*‖g k‖^2 ≤ ‖gradient J (w k)‖^2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hn 2
      have hg := gradient_gap J lam L hJ wstar hmin (w k)
      rw [hJstar,sub_zero] at hg
      have hc : 0 < lam/(2*L^2) := by positivity
      have hh := (mul_le_mul_of_nonneg_left hn2 hc.le).trans (hg.trans (hgeo k))
      have hden : 0 < lam/(2*L^2)*(1-θ)^2 := by positivity
      have hfinal : ‖g k‖^2 ≤ (q^k*J (w 0))/(lam/(2*L^2)*(1-θ)^2) := by
        apply (le_div_iff₀ hden).mpr
        nlinarith
      calc _ ≤ (q^k*J (w 0))/(lam/(2*L^2)*(1-θ)^2) := hfinal
        _ = _ := by dsimp [q,a]; field_simp <;> ring

#print axioms solution
