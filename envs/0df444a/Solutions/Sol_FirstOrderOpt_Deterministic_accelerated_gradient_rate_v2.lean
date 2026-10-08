-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.accelerated_gradient_rate_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:49:44.687291+00:00
-- url     : https://prove2.me/submissions/00aeb2e7-65f2-4637-afd6-cd9b4b2af53b

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

set_option autoImplicit false

namespace AGDRate3b65

open FirstOrderOpt.Prox

/-- Descent lemma along a convex set. -/
theorem descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (f : E → ℝ) (L : ℝ)
    (fGrad : E → E →L[ℝ] ℝ)
    (hGrad : ∀ x ∈ X, HasFDerivWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (x y : E) (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + fGrad x (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  let p : ℝ → E := fun s => x + s • d
  have hpX : ∀ s ∈ Set.Icc (0:ℝ) 1, p s ∈ X := by
    intro s hs
    have e : p s = (1 - s) • x + s • y := by
      simp only [p, d, smul_sub, sub_smul, one_smul]; abel
    rw [e]
    exact hXconv hx hy (by linarith [hs.2]) hs.1 (by ring)
  let φ : ℝ → ℝ := fun s => f (p s) - s * fGrad x d - L / 2 * s ^ 2 * ‖d‖ ^ 2
  let φ' : ℝ → ℝ := fun s => fGrad (p s) d - fGrad x d - L * s * ‖d‖ ^ 2
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt φ (φ' s) (Set.Icc 0 1) s := by
    intro s hs
    have hp : HasDerivWithinAt p d (Set.Icc 0 1) s := by
      have := ((hasDerivAt_id s).smul_const d).const_add x
      simpa [p] using this.hasDerivWithinAt
    have h1 : HasDerivWithinAt (f ∘ p) (fGrad (p s) d) (Set.Icc 0 1) s :=
      (hGrad (p s) (hpX s hs)).comp_hasDerivWithinAt s hp (fun r hr => hpX r hr)
    have h2 : HasDerivWithinAt (fun s : ℝ => s * fGrad x d) (fGrad x d) (Set.Icc 0 1) s := by
      simpa using ((hasDerivAt_id s).mul_const (fGrad x d)).hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun s : ℝ => L / 2 * s ^ 2 * ‖d‖ ^ 2) (L * s * ‖d‖ ^ 2)
        (Set.Icc 0 1) s := by
      have := (((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖d‖ ^ 2)).hasDerivWithinAt
        (s := Set.Icc (0:ℝ) 1)
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, show (2:ℕ) - 1 = 1 from rfl, pow_one]
      ring
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) (f' := φ')
    · intro s hs; exact (hderiv s hs).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs ⊢
      exact (hderiv s (Set.Ioo_subset_Icc_self hs)).mono Set.Ioo_subset_Icc_self
    · intro s hs
      rw [interior_Icc] at hs
      have hsX := hpX s (Set.Ioo_subset_Icc_self hs)
      have hb : fGrad (p s) d - fGrad x d ≤ ‖fGrad (p s) - fGrad x‖ * ‖d‖ := by
        have := (fGrad (p s) - fGrad x).le_opNorm d
        rw [ContinuousLinearMap.sub_apply, Real.norm_eq_abs] at this
        exact le_trans (le_abs_self _) this
      have hn : ‖fGrad (p s) - fGrad x‖ ≤ L * (s * ‖d‖) := by
        have := hSmooth (p s) hsX x hx
        have e : p s - x = s • d := by simp [p]
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1] at this
        exact this
      have := mul_le_mul_of_nonneg_right hn (norm_nonneg d)
      simp only [φ']
      nlinarith [norm_nonneg d]
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    zero_le_one
  have e1 : p 1 = y := by simp [p, d]
  have e0 : p 0 = x := by simp [p]
  simp only [φ] at h01
  rw [e1, e0] at h01
  norm_num at h01
  linarith

/-- Strong convexity lower bound for the Bregman distance. -/
theorem V_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ν : DistanceGeneratingFunction X) (u w : E) (hu : u ∈ X) (hw : w ∈ X) :
    (1 / 2) * ‖w - u‖ ^ 2 ≤ ν.V u w := by
  have := ν.strongConvex u hu w hw
  unfold DistanceGeneratingFunction.V
  linarith

/-- Three-point lemma from the minimality of the prox step. -/
theorem three_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (ν : DistanceGeneratingFunction X)
    (γ : ℝ) (g : E →L[ℝ] ℝ) (u w : E) (hw : w ∈ X)
    (hmin : ∀ y ∈ X, γ * g w + ν.V u w ≤ γ * g y + ν.V u y) :
    ∀ y ∈ X, γ * g w + ν.V u w + ν.V w y ≤ γ * g y + ν.V u y := by
  intro y hy
  let h : E → ℝ := fun z => γ * g z + ν.V u z
  have hloc : IsLocalMinOn h X w := IsMinOn.localize (fun z hz => hmin z hz)
  have hVeq : (fun z => ν.V u z) = fun z => (ν.ω z - ν.ω u) - (ν.dω u z - ν.dω u u) := by
    funext z; simp [DistanceGeneratingFunction.V, map_sub]
  have h1 : HasFDerivWithinAt (fun z => γ * g z) (γ • g) X w := by
    exact (g.hasFDerivWithinAt (s := X) (x := w)).const_mul γ
  have h2 : HasFDerivWithinAt (fun z => ν.V u z) (ν.dω w - ν.dω u) X w := by
    rw [hVeq]
    exact ((ν.hasFDerivWithinAt w hw).sub_const (ν.ω u)).sub
      (((ν.dω u).hasFDerivWithinAt).sub_const (ν.dω u u))
  have hder : HasFDerivWithinAt h (γ • g + (ν.dω w - ν.dω u)) X w := h1.add h2
  have hcone : y - w ∈ posTangentConeAt X w :=
    sub_mem_posTangentConeAt_of_segment_subset (hXconv.segment_subset hw hy)
  have hnn := hloc.hasFDerivWithinAt_nonneg hder hcone
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, map_sub, smul_eq_mul] at hnn
  unfold DistanceGeneratingFunction.V
  simp only [map_sub]
  nlinarith [hnn]

/-- The pure algebra of one step. -/
theorem alg (T L Fbar Fx Fb Fs gq gp gb gxs gx n Vp Vq Vpq : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (D : (T + 1) * Fbar ≤ (T + 1) * Fx + 2 * (gq - gp) + 2 * L * n ^ 2 / (T + 1))
    (G : (T + 1) * gx = (T - 1) * gb + 2 * gp) (C1 : Fx + (gb - gx) ≤ Fb)
    (C2 : Fx + (gxs - gx) ≤ Fs)
    (T3 : T * gq + 2 * L * (Vpq + Vq) ≤ T * gxs + 2 * L * Vp) (S : 1 / 2 * n ^ 2 ≤ Vpq) :
    T * (T + 1) * (Fbar - Fs) + 4 * L * Vq ≤ (T - 1) * T * (Fb - Fs) + 4 * L * Vp := by
  have hT0 : (0:ℝ) ≤ T := by linarith
  have hq : T * (2 * L * n ^ 2 / (T + 1)) ≤ 2 * L * n ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    have : 0 ≤ 2 * L * n ^ 2 := by positivity
    nlinarith
  have P1 := mul_le_mul_of_nonneg_left D hT0
  have P2 := mul_le_mul_of_nonneg_left C1 (show (0:ℝ) ≤ T * (T - 1) by nlinarith)
  have P3 := mul_le_mul_of_nonneg_left C2 (show (0:ℝ) ≤ 2 * T by linarith)
  have P4 : T * ((T + 1) * gx) = T * ((T - 1) * gb + 2 * gp) := by rw [G]
  have P5 := mul_le_mul_of_nonneg_left S (show (0:ℝ) ≤ 4 * L by linarith)
  nlinarith [P1, P2, P3, P4, P5, hq, T3]

end AGDRate3b65

open FirstOrderOpt.Prox in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (fGrad : E → E →L[ℝ] ℝ)
    (hGrad : ∀ x ∈ X, HasFDerivWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (hConvex : ∀ x ∈ X, ∀ y ∈ X, f x + (fGrad x) (y - x) ≤ f y)
    (x xTilde xBar : ℕ → E)
    (hx : ∀ t, x t ∈ X) (hxBar0 : xBar 0 = x 0)
    (k : ℕ) (hk : 1 ≤ k)
    (hTildeDef : ∀ t : ℕ, 1 ≤ t → t ≤ k →
      xTilde t = (1 - 2 / ((t : ℝ) + 1)) • xBar (t - 1) + (2 / ((t : ℝ) + 1)) • x (t - 1))
    (hxDef : ∀ t : ℕ, 1 ≤ t → t ≤ k → ∀ y ∈ X,
      ((t : ℝ) / (2 * L)) * (fGrad (xTilde t)) (x t) + ν.V (x (t - 1)) (x t) ≤
        ((t : ℝ) / (2 * L)) * (fGrad (xTilde t)) y + ν.V (x (t - 1)) y)
    (hBarDef : ∀ t : ℕ, 1 ≤ t → t ≤ k →
      xBar t = (1 - 2 / ((t : ℝ) + 1)) • xBar (t - 1) + (2 / ((t : ℝ) + 1)) • x t)
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, f xstar ≤ f y) :
    f (xBar k) - f xstar ≤ (4 * L) / ((k : ℝ) * ((k : ℝ) + 1)) * ν.V (x 0) xstar := by
  have hcoef : ∀ t : ℕ, 1 ≤ t → (0:ℝ) ≤ 2 / ((t:ℝ) + 1) ∧ 2 / ((t:ℝ) + 1) ≤ 1 := by
    intro t ht
    have : (1:ℝ) ≤ t := by exact_mod_cast ht
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]; linarith
  have hBarX : ∀ t, t ≤ k → xBar t ∈ X := by
    intro t
    induction t with
    | zero => intro _; rw [hxBar0]; exact hx 0
    | succ n ih =>
      intro hn
      rw [hBarDef (n + 1) (by omega) hn]
      obtain ⟨h0, h1⟩ := hcoef (n + 1) (by omega)
      have := ih (by omega)
      simp only [Nat.add_sub_cancel]
      exact hXconv this (hx (n + 1)) (by linarith) h0 (by ring)
  have hTildeX : ∀ t, 1 ≤ t → t ≤ k → xTilde t ∈ X := by
    intro t h1 h2
    rw [hTildeDef t h1 h2]
    obtain ⟨a0, a1⟩ := hcoef t h1
    exact hXconv (hBarX (t - 1) (by omega)) (hx (t - 1)) (by linarith) a0 (by ring)
  have step : ∀ t : ℕ, 1 ≤ t → t ≤ k →
      (t:ℝ) * ((t:ℝ) + 1) * (f (xBar t) - f xstar) + 4 * L * ν.V (x t) xstar ≤
        ((t:ℝ) - 1) * (t:ℝ) * (f (xBar (t - 1)) - f xstar) + 4 * L * ν.V (x (t - 1)) xstar := by
    intro t h1 h2
    have hT : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast h1
    have hα0 : (0:ℝ) < 2 / ((t:ℝ) + 1) := by positivity
    have hbX : xBar (t - 1) ∈ X := hBarX (t - 1) (by omega)
    have hxtX : xTilde t ∈ X := hTildeX t h1 h2
    have hdiff : xBar t - xTilde t = (2 / ((t:ℝ) + 1)) • (x t - x (t - 1)) := by
      rw [hBarDef t h1 h2, hTildeDef t h1 h2, smul_sub]; abel
    have D0 := AGDRate3b65.descent X hXconv f L fGrad hGrad hSmooth (xTilde t) (xBar t) hxtX
      (hBarX t h2)
    rw [hdiff, map_smul, map_sub, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hα0] at D0
    have keyD : ((t:ℝ) + 1) * (f (xTilde t) + 2 / ((t:ℝ) + 1) *
        (fGrad (xTilde t) (x t) - fGrad (xTilde t) (x (t - 1))) +
          L / 2 * (2 / ((t:ℝ) + 1) * ‖x t - x (t - 1)‖) ^ 2) =
        ((t:ℝ) + 1) * f (xTilde t) +
          2 * (fGrad (xTilde t) (x t) - fGrad (xTilde t) (x (t - 1))) +
          2 * L * ‖x t - x (t - 1)‖ ^ 2 / ((t:ℝ) + 1) := by
      first | (field_simp; done) | (field_simp; ring)
    have D : ((t:ℝ) + 1) * f (xBar t) ≤
        ((t:ℝ) + 1) * f (xTilde t) +
          2 * (fGrad (xTilde t) (x t) - fGrad (xTilde t) (x (t - 1))) +
          2 * L * ‖x t - x (t - 1)‖ ^ 2 / ((t:ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_left D0 (show (0:ℝ) ≤ (t:ℝ) + 1 by linarith)
      linarith [keyD]
    have G : ((t:ℝ) + 1) * fGrad (xTilde t) (xTilde t) =
        ((t:ℝ) - 1) * fGrad (xTilde t) (xBar (t - 1)) + 2 * fGrad (xTilde t) (x (t - 1)) := by
      have e : fGrad (xTilde t) (xTilde t) = fGrad (xTilde t)
          ((1 - 2 / ((t : ℝ) + 1)) • xBar (t - 1) + (2 / ((t : ℝ) + 1)) • x (t - 1)) :=
        congrArg (fGrad (xTilde t)) (hTildeDef t h1 h2)
      rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      first | (field_simp; done) | (field_simp; ring)
    have C1 := hConvex (xTilde t) hxtX (xBar (t - 1)) hbX
    have C2 := hConvex (xTilde t) hxtX xstar hxstar
    rw [map_sub] at C1 C2
    have T3 := AGDRate3b65.three_point X hXconv ν ((t:ℝ) / (2 * L)) (fGrad (xTilde t))
      (x (t - 1)) (x t) (hx t) (hxDef t h1 h2) xstar hxstar
    have T3' : (t:ℝ) * fGrad (xTilde t) (x t) +
        2 * L * (ν.V (x (t - 1)) (x t) + ν.V (x t) xstar) ≤
        (t:ℝ) * fGrad (xTilde t) xstar + 2 * L * ν.V (x (t - 1)) xstar := by
      have := mul_le_mul_of_nonneg_left T3 (show (0:ℝ) ≤ 2 * L by linarith)
      have hL0 : L ≠ 0 := hL.ne'
      have e1 : 2 * L * ((t:ℝ) / (2 * L) * fGrad (xTilde t) (x t) + ν.V (x (t - 1)) (x t) +
          ν.V (x t) xstar) =
          (t:ℝ) * fGrad (xTilde t) (x t) + 2 * L * (ν.V (x (t - 1)) (x t) + ν.V (x t) xstar) := by
        first | (field_simp; done) | (field_simp; ring)
      have e2 : 2 * L * ((t:ℝ) / (2 * L) * fGrad (xTilde t) xstar + ν.V (x (t - 1)) xstar) =
          (t:ℝ) * fGrad (xTilde t) xstar + 2 * L * ν.V (x (t - 1)) xstar := by
        first | (field_simp; done) | (field_simp; ring)
      linarith
    have S := AGDRate3b65.V_ge X ν (x (t - 1)) (x t) (hx (t - 1)) (hx t)
    exact AGDRate3b65.alg (t:ℝ) L (f (xBar t)) (f (xTilde t)) (f (xBar (t - 1))) (f xstar)
      (fGrad (xTilde t) (x t)) (fGrad (xTilde t) (x (t - 1))) (fGrad (xTilde t) (xBar (t - 1)))
      (fGrad (xTilde t) xstar) (fGrad (xTilde t) (xTilde t)) ‖x t - x (t - 1)‖
      (ν.V (x (t - 1)) xstar) (ν.V (x t) xstar) (ν.V (x (t - 1)) (x t)) hT hL D G C1 C2 T3' S
  have tele : ∀ t : ℕ, t ≤ k →
      (t:ℝ) * ((t:ℝ) + 1) * (f (xBar t) - f xstar) + 4 * L * ν.V (x t) xstar ≤
        4 * L * ν.V (x 0) xstar := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hs := step (n + 1) (by omega) hn
      have hi := ih (by omega)
      simp only [Nat.add_sub_cancel] at hs
      push_cast at hs
      have e : ((n:ℝ) + 1 - 1) = n := by ring
      rw [e] at hs
      push_cast
      linarith
  have hk' := tele k le_rfl
  have hVk := AGDRate3b65.V_ge X ν (x k) xstar (hx k) hxstar
  have hkpos : (0:ℝ) < (k:ℝ) * ((k:ℝ) + 1) := by
    have : (1:ℝ) ≤ k := by exact_mod_cast hk
    positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hkpos]
  have : 0 ≤ 4 * L * ν.V (x k) xstar := by
    have : 0 ≤ (1 / 2) * ‖xstar - x k‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hVk (show (0:ℝ) ≤ 4 * L by linarith)
    nlinarith
  nlinarith
