-- Prove2me | solution 1 for BotNguyenADMM.Rates.theorem_18
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:24:13.836919+00:00
-- url     : https://prove2.me/submissions/e7a865d0-b670-49e8-933c-4cef6cedcb2a

import Mathlib
import Definitions.Def_BotNguyenADMM_Rates_Setting
import Definitions.Def_BotNguyenADMM_Rates_Lojasiewicz
import Theorems.Thm_BotNguyenADMM_Rates_lemma_15

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace
open NonconvexSplitting.Shared

set_option autoImplicit false

section Helpers

open BotNguyenADMM.KL

private noncomputable def hpOf {n m : ℕ} (v : Variant) (P : Data n m) (xk u : E n) : ℝ :=
  match v with
  | .prox => P.h u
  | .linearized => ⟪u - xk, gradient P.h xk⟫

private noncomputable def gxOf {n m : ℕ} (v : Variant) (P : Data n m) (xk xk1 : E n) : E n :=
  match v with
  | .prox => gradient P.h xk1
  | .linearized => gradient P.h xk

private lemma xObj_eq' {n m : ℕ} (v : Variant) (P : Data n m) (k : ℕ) (xk : E n) (zk1 yk : E m)
    (u : E n) :
    xObj v P k xk zk1 yk u = hpOf v P xk u + ⟪yk, P.A u - zk1⟫ + P.r / 2 * ‖P.A u - zk1‖ ^ 2
      + 1 / 2 * ⟪P.M₁ k (u - xk), u - xk⟫ := by
  cases v <;> rfl

private lemma hpOf_deriv {n m : ℕ} (v : Variant) (P : Data n m) (hd : Differentiable ℝ P.h)
    (xk u0 d : E n) :
    HasDerivAt (fun t : ℝ => hpOf v P xk (u0 + t • d)) ⟪gxOf v P xk u0, d⟫ 0 := by
  have hℓ : HasDerivAt (fun t : ℝ => u0 + t • d) d 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add u0
    simpa using this
  cases v with
  | prox =>
    have hd' : HasFDerivAt P.h (fderiv ℝ P.h (u0 + (0 : ℝ) • d)) (u0 + (0 : ℝ) • d) :=
      (hd _).hasFDerivAt
    have := hd'.comp_hasDerivAt (0 : ℝ) hℓ
    have e : fderiv ℝ P.h u0 d = ⟪gradient P.h u0, d⟫ := by
      unfold gradient
      rw [InnerProductSpace.toDual_symm_apply]
    simp only [zero_smul, add_zero] at this
    rw [e] at this
    exact this
  | linearized =>
    have h1 : HasDerivAt (fun t : ℝ => u0 + t • d - xk) d 0 := hℓ.sub_const xk
    have h2 := h1.inner ℝ (hasDerivAt_const (0 : ℝ) (gradient P.h xk))
    simpa [hpOf, gxOf] using h2

private lemma xopt {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    gxOf v P (x k) (x (k + 1))
      + ContinuousLinearMap.adjoint P.A (y k + P.r • (P.A (x (k + 1)) - z (k + 1)))
      + P.M₁ k (x (k + 1) - x k) = 0 := by
  obtain ⟨_, hxmin, _⟩ := hrun k
  set u0 := x (k + 1) with hu0
  set G : E n := gxOf v P (x k) u0
      + ContinuousLinearMap.adjoint P.A (y k + P.r • (P.A u0 - z (k + 1)))
      + P.M₁ k (u0 - x k) with hG
  have hsymm : ∀ a b : E n, ⟪P.M₁ k a, b⟫ = ⟪a, P.M₁ k b⟫ :=
    fun a b => (hA.M₁_pos k).isSymmetric a b
  have key : ∀ d : E n, ⟪G, d⟫ = 0 := by
    intro d
    have hℓ : HasDerivAt (fun t : ℝ => u0 + t • d) d 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add u0
      simpa using this
    have hmin : IsLocalMin (fun t : ℝ => xObj v P k (x k) (z (k + 1)) (y k) (u0 + t • d)) 0 := by
      refine Filter.Eventually.of_forall (fun t => ?_)
      have := hxmin (u0 + t • d)
      simpa using this
    have hAℓ : HasDerivAt (fun t : ℝ => P.A (u0 + t • d) - z (k + 1)) (P.A d) 0 := by
      have := P.A.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hℓ
      exact this.sub_const (z (k + 1))
    have hq : HasDerivAt (fun t : ℝ => ‖P.A (u0 + t • d) - z (k + 1)‖ ^ 2)
        (2 * ⟪P.A u0 - z (k + 1), P.A d⟫) 0 := by
      have := hAℓ.norm_sq
      simpa using this
    have hin : HasDerivAt (fun t : ℝ => ⟪y k, P.A (u0 + t • d) - z (k + 1)⟫) ⟪y k, P.A d⟫ 0 := by
      have := (hasDerivAt_const (0 : ℝ) (y k)).inner ℝ hAℓ
      simpa using this
    have hℓ' : HasDerivAt (fun t : ℝ => u0 + t • d - x k) d 0 := hℓ.sub_const (x k)
    have hM : HasDerivAt (fun t : ℝ => P.M₁ k (u0 + t • d - x k)) (P.M₁ k d) 0 :=
      (P.M₁ k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hℓ'
    have hquad : HasDerivAt (fun t : ℝ => ⟪P.M₁ k (u0 + t • d - x k), u0 + t • d - x k⟫)
        (⟪P.M₁ k (u0 - x k), d⟫ + ⟪P.M₁ k d, u0 - x k⟫) 0 := by
      have := hM.inner ℝ hℓ'
      simpa using this
    have hquad' : (⟪P.M₁ k (u0 - x k), d⟫ + ⟪P.M₁ k d, u0 - x k⟫) = 2 * ⟪P.M₁ k (u0 - x k), d⟫ := by
      rw [hsymm d (u0 - x k), real_inner_comm]; ring
    have hmain := hpOf_deriv v P hA.h_diff (x k) u0 d
    have hall := ((hmain.add hin).add (hq.const_mul (P.r / 2))).add (hquad.const_mul (1 / 2))
    have hxo : (fun t : ℝ => xObj v P k (x k) (z (k + 1)) (y k) (u0 + t • d)) =
        (((fun t : ℝ => hpOf v P (x k) (u0 + t • d)) + fun t : ℝ => ⟪y k, P.A (u0 + t • d) - z (k + 1)⟫)
          + fun t : ℝ => P.r / 2 * ‖P.A (u0 + t • d) - z (k + 1)‖ ^ 2)
          + fun t : ℝ => 1 / 2 * ⟪P.M₁ k (u0 + t • d - x k), u0 + t • d - x k⟫ := by
      funext t; simp only [xObj_eq', Pi.add_apply]
    rw [hxo] at hmin
    have h0 := hmin.hasDerivAt_eq_zero hall
    rw [hquad'] at h0
    have hGd : ⟪G, d⟫ = ⟪gxOf v P (x k) u0, d⟫ + ⟪y k, P.A d⟫
          + P.r / 2 * (2 * ⟪P.A u0 - z (k + 1), P.A d⟫) + 1 / 2 * (2 * ⟪P.M₁ k (u0 - x k), d⟫) := by
      rw [hG]
      simp only [inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
      ring
    rw [hGd]; exact h0
  have h2 := key G
  rw [real_inner_self_eq_norm_sq] at h2
  exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h2)

private lemma hy_rel {n m : ℕ} {v : Variant} {P : Data n m} {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun v P x z y) (k : ℕ) :
    y (k + 1) - y k = (P.ρ * P.r) • (P.A (x (k + 1)) - z (k + 1)) := by
  rw [(hrun k).2.2]; abel

private lemma hQ_rel {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    gxOf v P (x k) (x (k + 1)) + P.M₁ k (x (k + 1) - x k)
      + ContinuousLinearMap.adjoint P.A (y k)
      + (1 / P.ρ) • ContinuousLinearMap.adjoint P.A (y (k + 1) - y k) = 0 := by
  have h := xopt v P hA x z y hrun k
  have hρ : P.ρ ≠ 0 := hA.ρ_pos.ne'
  have hr : P.r ≠ 0 := hA.r_pos.ne'
  have he : P.r • (P.A (x (k + 1)) - z (k + 1)) = (1 / P.ρ) • (y (k + 1) - y k) := by
    rw [hy_rel hrun k, smul_smul]; congr 1; field_simp
  have he' : P.r • ContinuousLinearMap.adjoint P.A (P.A (x (k + 1)) - z (k + 1))
      = (1 / P.ρ) • ContinuousLinearMap.adjoint P.A (y (k + 1) - y k) := by
    rw [← map_smul, he, map_smul]
  rw [map_add, map_smul, he'] at h
  have key : gxOf v P (x k) (x (k + 1)) + P.M₁ k (x (k + 1) - x k)
      + ContinuousLinearMap.adjoint P.A (y k)
      + (1 / P.ρ) • ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)
      = gxOf v P (x k) (x (k + 1))
      + (ContinuousLinearMap.adjoint P.A (y k) + (1 / P.ρ) • ContinuousLinearMap.adjoint P.A (y (k + 1) - y k))
      + P.M₁ k (x (k + 1) - x k) := by abel
  rw [key]; exact h

private noncomputable def kapA {n m : ℕ} (v : Variant) (P : Data n m) : ℝ :=
  match v with
  | .prox => P.L + P.μ₁
  | .linearized => P.μ₁

private noncomputable def kapB {n m : ℕ} (v : Variant) (P : Data n m) : ℝ :=
  match v with
  | .prox => P.μ₁
  | .linearized => P.L + P.μ₁

private lemma C1_eq {n m : ℕ} (v : Variant) (P : Data n m) :
    C1 v P = 4 * T0 P * kapB v P ^ 2 / P.r := by cases v <;> rfl

private lemma CMprime_eq {n m : ℕ} (v : Variant) (P : Data n m) :
    BotNguyenADMM.Rates.CMprime v P.L P.μ₁ P.lam P.ρ =
      (8 * kapA v P ^ 2 + 10 * kapB v P ^ 2) * T0 P := by
  cases v <;> simp only [BotNguyenADMM.Rates.CMprime, kapA, kapB] <;>
    change _ = (8 * _ + 10 * _) * BotNguyenADMM.Rates.T0 P.lam P.ρ <;> ring

private lemma M1_norm_le {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (k : ℕ) (d : E n) :
    ‖P.M₁ k d‖ ≤ P.μ₁ * ‖d‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hA.μ₁_bound k) (norm_nonneg _))

private lemma dQ_bound {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (j : ℕ) :
    ‖(gxOf v P (x (j + 1)) (x (j + 2)) + P.M₁ (j + 1) (x (j + 2) - x (j + 1)))
        - (gxOf v P (x j) (x (j + 1)) + P.M₁ j (x (j + 1) - x j))‖
      ≤ kapA v P * ‖x (j + 2) - x (j + 1)‖ + kapB v P * ‖x (j + 1) - x j‖ := by
  have m1 := M1_norm_le v P hA (j + 1) (x (j + 2) - x (j + 1))
  have m0 := M1_norm_le v P hA j (x (j + 1) - x j)
  cases v with
  | prox =>
    have hl := hA.h_lip (x (j + 2)) (x (j + 1))
    have e : (gxOf Variant.prox P (x (j + 1)) (x (j + 2)) + P.M₁ (j + 1) (x (j + 2) - x (j + 1)))
        - (gxOf Variant.prox P (x j) (x (j + 1)) + P.M₁ j (x (j + 1) - x j))
        = (gradient P.h (x (j + 2)) - gradient P.h (x (j + 1))) + P.M₁ (j + 1) (x (j + 2) - x (j + 1))
          - P.M₁ j (x (j + 1) - x j) := by simp only [gxOf]; abel
    rw [e]
    calc _ ≤ ‖gradient P.h (x (j + 2)) - gradient P.h (x (j + 1))‖ + ‖P.M₁ (j + 1) (x (j + 2) - x (j + 1))‖
          + ‖P.M₁ j (x (j + 1) - x j)‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
      _ ≤ P.L * ‖x (j + 2) - x (j + 1)‖ + P.μ₁ * ‖x (j + 2) - x (j + 1)‖ + P.μ₁ * ‖x (j + 1) - x j‖ := by
          gcongr
      _ = _ := by simp [kapA, kapB]; ring
  | linearized =>
    have hl := hA.h_lip (x (j + 1)) (x j)
    have e : (gxOf Variant.linearized P (x (j + 1)) (x (j + 2)) + P.M₁ (j + 1) (x (j + 2) - x (j + 1)))
        - (gxOf Variant.linearized P (x j) (x (j + 1)) + P.M₁ j (x (j + 1) - x j))
        = (gradient P.h (x (j + 1)) - gradient P.h (x j)) + P.M₁ (j + 1) (x (j + 2) - x (j + 1))
          - P.M₁ j (x (j + 1) - x j) := by simp only [gxOf]; abel
    rw [e]
    calc _ ≤ ‖gradient P.h (x (j + 1)) - gradient P.h (x j)‖ + ‖P.M₁ (j + 1) (x (j + 2) - x (j + 1))‖
          + ‖P.M₁ j (x (j + 1) - x j)‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
      _ ≤ P.L * ‖x (j + 1) - x j‖ + P.μ₁ * ‖x (j + 2) - x (j + 1)‖ + P.μ₁ * ‖x (j + 1) - x j‖ := by
          gcongr
      _ = _ := by simp [kapA, kapB]; ring

private lemma B_rec {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (j : ℕ) :
    ContinuousLinearMap.adjoint P.A (y (j + 2) - y (j + 1))
      = (1 - P.ρ) • ContinuousLinearMap.adjoint P.A (y (j + 1) - y j)
        - P.ρ • ((gxOf v P (x (j + 1)) (x (j + 2)) + P.M₁ (j + 1) (x (j + 2) - x (j + 1)))
          - (gxOf v P (x j) (x (j + 1)) + P.M₁ j (x (j + 1) - x j))) := by
  have e1 := hQ_rel v P hA x z y hrun (j + 1)
  have e0 := hQ_rel v P hA x z y hrun j
  have hρ : P.ρ ≠ 0 := hA.ρ_pos.ne'
  have hd : ContinuousLinearMap.adjoint P.A (y (j + 1)) - ContinuousLinearMap.adjoint P.A (y j)
      = ContinuousLinearMap.adjoint P.A (y (j + 1) - y j) := (map_sub _ _ _).symm
  set B1 := ContinuousLinearMap.adjoint P.A (y (j + 1 + 1) - y (j + 1))
  set B0 := ContinuousLinearMap.adjoint P.A (y (j + 1) - y j)
  set Q1 := gxOf v P (x (j + 1)) (x (j + 1 + 1)) + P.M₁ (j + 1) (x (j + 1 + 1) - x (j + 1))
  set Q0 := gxOf v P (x j) (x (j + 1)) + P.M₁ j (x (j + 1) - x j)
  set a1 := ContinuousLinearMap.adjoint P.A (y (j + 1))
  set a0 := ContinuousLinearMap.adjoint P.A (y j)
  have hB1' : B1 = -(P.ρ • Q1) - P.ρ • a1 := by
    have := congrArg (fun w => P.ρ • w) e1
    simp only [smul_add, smul_smul, smul_zero] at this
    rw [mul_one_div_cancel hρ, one_smul] at this
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← this]; abel
  have hB0' : B0 = -(P.ρ • Q0) - P.ρ • a0 := by
    have := congrArg (fun w => P.ρ • w) e0
    simp only [smul_add, smul_smul, smul_zero] at this
    rw [mul_one_div_cancel hρ, one_smul] at this
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← this]; abel
  have ha1' : a1 = a0 + B0 := by rw [← hd]; abel
  have this : P.ρ • a0 = -(P.ρ • Q0) - B0 := by rw [hB0']; abel
  have h5 : P.ρ • (a0 + B0) = P.ρ • a0 + P.ρ • B0 := smul_add _ _ _
  rw [hB1', ha1', h5, this, sub_smul, one_smul, smul_sub]
  abel

private lemma bn_descent_abstract {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (h : V → ℝ) (G : V → V) (L : ℝ)
    (hder : ∀ p d : V, HasDerivAt (fun t : ℝ => h (p + t • d)) (inner ℝ (G p) d) 0)
    (hL : ∀ p q, ‖G p - G q‖ ≤ L * ‖p - q‖) (p q : V) :
    h q ≤ h p + inner ℝ (G p) (q - p) + L / 2 * ‖q - p‖ ^ 2 := by
  set d : V := q - p with hd
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => h (p + s • d)) (inner ℝ (G (p + t • d)) d) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => h (p + t • d + s • d)) (inner ℝ (G (p + t • d)) d)
        (t + -t) := by simpa using hder (p + t • d) d
    have h2 := h1.comp_add_const t (-t)
    have h3 : (fun s : ℝ => h (p + t • d + (s + -t) • d)) = fun s : ℝ => h (p + s • d) := by
      funext s; congr 1; rw [add_smul, neg_smul]; abel
    rwa [h3] at h2
  set g : ℝ → ℝ := fun t => h (p + t • d) - h p - t * inner ℝ (G p) d - L * ‖d‖ ^ 2 / 2 * t ^ 2
    with hg
  have hg' : ∀ t : ℝ, HasDerivAt g (inner ℝ (G (p + t • d)) d - inner ℝ (G p) d
      - L * ‖d‖ ^ 2 * t) t := by
    intro t
    have := (((hφ t).sub_const (h p)).sub ((hasDerivAt_id t).mul_const (inner ℝ (G p) d))).sub
      (((hasDerivAt_pow 2 t).const_mul (L * ‖d‖ ^ 2 / 2)))
    have hgd : HasDerivAt g (inner ℝ (G (p + t • d)) d - 1 * inner ℝ (G p) d
        - L * ‖d‖ ^ 2 / 2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1))) t := this
    refine hgd.congr_deriv ?_
    norm_num; ring
  have hanti : AntitoneOn g (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun t _ => (hg' t).continuousAt.continuousWithinAt)
      (fun t _ => (hg' t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [(hg' t).deriv]
    have ht0 : 0 ≤ t := by rw [interior_Icc] at ht; exact ht.1.le
    have h1 : inner ℝ (G (p + t • d) - G p) d ≤ L * (t * ‖d‖ ^ 2) := by
      calc inner ℝ (G (p + t • d) - G p) d ≤ ‖G (p + t • d) - G p‖ * ‖d‖ := real_inner_le_norm _ _
        _ ≤ (L * ‖(p + t • d) - p‖) * ‖d‖ := by gcongr; exact hL _ _
        _ = L * (t * ‖d‖ ^ 2) := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]; ring
    rw [inner_sub_left] at h1
    nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [hg, one_smul, zero_smul, add_zero, zero_mul, sub_zero, one_mul, one_pow, mul_zero,
    zero_pow two_ne_zero] at this
  have hpq : p + d = q := by rw [hd]; abel
  rw [hpq] at this
  nlinarith

private lemma h_hasDeriv {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (p d : E n) :
    HasDerivAt (fun t : ℝ => P.h (p + t • d)) ⟪gradient P.h p, d⟫ 0 := by
  have := hpOf_deriv Variant.prox P hA.h_diff p p d
  simpa [hpOf, gxOf] using this

private lemma h_up {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (p q : E n) :
    P.h q ≤ P.h p + ⟪gradient P.h p, q - p⟫ + P.L / 2 * ‖q - p‖ ^ 2 :=
  bn_descent_abstract P.h (gradient P.h) P.L (fun p d => h_hasDeriv v P hA p d) hA.h_lip p q

private lemma h_low {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (p q : E n) :
    P.h p + ⟪gradient P.h p, q - p⟫ - P.L / 2 * ‖q - p‖ ^ 2 ≤ P.h q := by
  have := bn_descent_abstract (fun u => -P.h u) (fun u => -gradient P.h u) P.L
    (fun p d => by
      rw [inner_neg_left]
      exact (h_hasDeriv v P hA p d).neg)
    (fun p q => by
      rw [show -gradient P.h p - -gradient P.h q = -(gradient P.h p - gradient P.h q) by abel,
        norm_neg]
      exact hA.h_lip p q) p q
  simp only [inner_neg_left] at this
  linarith

private lemma h_gx {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (k : ℕ) :
    P.h (x (k + 1)) - P.h (x k) ≤
      ⟪gxOf v P (x k) (x (k + 1)), x (k + 1) - x k⟫ + P.L / 2 * ‖x (k + 1) - x k‖ ^ 2 := by
  cases v with
  | prox =>
    have h := h_low Variant.prox P hA (x (k + 1)) (x k)
    have e1 : x k - x (k + 1) = -(x (k + 1) - x k) := by abel
    rw [e1, inner_neg_right, norm_neg] at h
    simp only [gxOf]; linarith
  | linearized =>
    have h := h_up Variant.linearized P hA (x k) (x (k + 1))
    simp only [gxOf]; linarith

private noncomputable def R3 {n m : ℕ} (P : Data n m) (x : E n) (z y : E m) : ℝ :=
  P.h x + ⟪y, P.A x - z⟫ + P.r / 2 * ‖P.A x - z‖ ^ 2

private lemma x_step {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    R3 P (x (k + 1)) (z (k + 1)) (y k)
      + 1 / 2 * (2 * ⟪P.M₁ k (x (k + 1) - x k), x (k + 1) - x k⟫
        + P.r * ‖P.A (x (k + 1) - x k)‖ ^ 2 - P.L * ‖x (k + 1) - x k‖ ^ 2)
      ≤ R3 P (x k) (z (k + 1)) (y k) := by
  have hopt := xopt v P hA x z y hrun k
  set Δ := x (k + 1) - x k with hΔ
  set p := P.A (x (k + 1)) - z (k + 1) with hp
  have hq : P.A (x k) - z (k + 1) = p - P.A Δ := by rw [hp, hΔ, map_sub]; abel
  have hin := congrArg (fun w => ⟪w, Δ⟫) hopt
  simp only [inner_add_left, ContinuousLinearMap.adjoint_inner_left, inner_zero_left,
    real_inner_smul_left] at hin
  have hhx := h_gx v P hA x k
  rw [← hΔ] at hhx
  have L1 : R3 P (x k) (z (k + 1)) (y k) = P.h (x k) + (⟪y k, p⟫ - ⟪y k, P.A Δ⟫)
      + P.r / 2 * (‖p‖ ^ 2 - 2 * ⟪p, P.A Δ⟫ + ‖P.A Δ‖ ^ 2) := by
    unfold R3; rw [hq, inner_sub_right, norm_sub_sq_real]
  have L2 : R3 P (x (k + 1)) (z (k + 1)) (y k) = P.h (x (k + 1)) + ⟪y k, p⟫ + P.r / 2 * ‖p‖ ^ 2 := rfl
  rw [L1, L2]
  nlinarith

private lemma y_step {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    R3 P (x (k + 1)) (z (k + 1)) (y (k + 1))
      = R3 P (x (k + 1)) (z (k + 1)) (y k) + ‖y (k + 1) - y k‖ ^ 2 / (P.ρ * P.r) := by
  have hpos : 0 < P.ρ * P.r := mul_pos hA.ρ_pos hA.r_pos
  have hy := hy_rel hrun k
  have this : ⟪y (k + 1) - y k, P.A (x (k + 1)) - z (k + 1)⟫ = ‖y (k + 1) - y k‖ ^ 2 / (P.ρ * P.r) := by
    have h2 : P.A (x (k + 1)) - z (k + 1) = (1 / (P.ρ * P.r)) • (y (k + 1) - y k) := by
      rw [hy, smul_smul, one_div_mul_cancel hpos.ne', one_smul]
    rw [h2, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have e2 : ⟪y (k + 1), P.A (x (k + 1)) - z (k + 1)⟫ = ⟪y k, P.A (x (k + 1)) - z (k + 1)⟫
      + ⟪y (k + 1) - y k, P.A (x (k + 1)) - z (k + 1)⟫ := by
    rw [← inner_add_left]; congr 1; abel
  unfold R3
  rw [e2, this]; ring

private lemma gz_fin {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    P.g (z (k + 1)) ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hA.g_proper.2
  intro htop
  have h := (hrun k).1 w
  unfold zObj at h
  rw [htop, EReal.top_add_coe] at h
  have h2 := top_le_iff.1 h
  rw [← EReal.coe_toReal hw (hA.g_proper.1 w), ← EReal.coe_add] at h2
  exact EReal.coe_ne_top _ h2

private lemma gz_eq {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    P.g (z (k + 1)) = (((P.g (z (k + 1))).toReal : ℝ) : EReal) :=
  (EReal.coe_toReal (gz_fin v P hA x z y hrun k) (hA.g_proper.1 _)).symm

private noncomputable def Phi {n m : ℕ} (P : Data n m) (k : ℕ) (xk : E n) (zk yk : E m) (w : E m) : ℝ :=
  ⟪yk, P.A xk - w⟫ + P.r / 2 * ‖P.A xk - w‖ ^ 2 + 1 / 2 * ⟪P.M₂ k (w - zk), w - zk⟫

private lemma z_step {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) (w : E m) (gw : ℝ)
    (hgw : P.g w = (gw : EReal)) :
    (P.g (z (k + 1))).toReal + Phi P k (x k) (z k) (y k) (z (k + 1))
      ≤ gw + Phi P k (x k) (z k) (y k) w := by
  have h := (hrun k).1 w
  unfold zObj at h
  rw [hgw, gz_eq v P hA x z y hrun k, ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h
  exact h

private lemma T0_pos {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) : 0 < T0 P := by
  have hl := hA.lam_pos; have h0 := hA.ρ_pos; have h2 := hA.ρ_lt
  unfold T0; split_ifs
  · positivity
  · have : 0 < 2 - P.ρ := by linarith
    positivity

private lemma L_pos {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) : 0 < P.L := by
  have h1 := hA.eq14.2; have h2 := T0_pos v P hA
  by_contra hc; push Not at hc
  nlinarith

private lemma T1_nonneg {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) : 0 ≤ T1 P := by
  have hl := hA.lam_pos; have h0 := hA.ρ_pos; have h2 := hA.ρ_lt; have hr := hA.r_pos
  unfold T1; split_ifs with h
  · apply div_nonneg <;> nlinarith [mul_pos (mul_pos hl (mul_pos h0 h0)) hr]
  · push Not at h
    apply div_nonneg
    · linarith
    · have : 0 < 2 - P.ρ := by linarith
      positivity

private lemma C1_nonneg {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) :
    0 ≤ C1 v P := by
  rw [C1_eq]; have := T0_pos v P hA; have := hA.r_pos; positivity

private lemma T_ineq {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (E α ek : ℝ)
    (hek0 : 0 ≤ ek) (hek : ek ≤ |1 - P.ρ| * E + P.ρ * α) :
    ek ^ 2 / (P.lam * P.ρ * P.r) + T1 P * ek ^ 2 ≤ T1 P * E ^ 2 + T0 P / P.r * α ^ 2 := by
  have hl := hA.lam_pos; have h0 := hA.ρ_pos; have h2 := hA.ρ_lt; have hr := hA.r_pos
  unfold T0 T1
  split_ifs with h
  · rw [abs_of_nonneg (by linarith)] at hek
    have hsq : ek ^ 2 ≤ (1 - P.ρ) * E ^ 2 + P.ρ * α ^ 2 := by
      have h1 : ek ^ 2 ≤ ((1 - P.ρ) * E + P.ρ * α) ^ 2 := pow_le_pow_left₀ hek0 hek 2
      nlinarith [mul_nonneg (mul_nonneg h0.le (by linarith : (0 : ℝ) ≤ 1 - P.ρ)) (sq_nonneg (E - α))]
    have eL : ek ^ 2 / (P.lam * P.ρ * P.r) + (1 - P.ρ) / (P.lam * P.ρ ^ 2 * P.r) * ek ^ 2
        = ek ^ 2 / (P.lam * P.ρ ^ 2 * P.r) := by field_simp; ring
    have eR : (1 - P.ρ) / (P.lam * P.ρ ^ 2 * P.r) * E ^ 2 + 1 / (P.lam * P.ρ) / P.r * α ^ 2
        = ((1 - P.ρ) * E ^ 2 + P.ρ * α ^ 2) / (P.lam * P.ρ ^ 2 * P.r) := by field_simp
    rw [eL, eR]
    exact div_le_div_of_nonneg_right hsq (by positivity)
  · push Not at h
    rw [abs_of_neg (by linarith)] at hek
    have hb : 0 < 2 - P.ρ := by linarith
    have hek' : ek ≤ (P.ρ - 1) * E + P.ρ * α := by linarith
    have hsq : ek ^ 2 * (2 - P.ρ) ≤ (P.ρ - 1) * (2 - P.ρ) * E ^ 2 + P.ρ ^ 2 * α ^ 2 := by
      have h1 : ek ^ 2 ≤ ((P.ρ - 1) * E + P.ρ * α) ^ 2 := pow_le_pow_left₀ hek0 hek' 2
      have h3 : ((P.ρ - 1) * E + P.ρ * α) ^ 2 * (2 - P.ρ)
          ≤ (P.ρ - 1) * (2 - P.ρ) * E ^ 2 + P.ρ ^ 2 * α ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ P.ρ - 1) hb.le)
          (sq_nonneg ((2 - P.ρ) * E - P.ρ * α))]
      nlinarith
    have eL : ek ^ 2 / (P.lam * P.ρ * P.r) + (P.ρ - 1) / (P.lam * (2 - P.ρ) * P.ρ * P.r) * ek ^ 2
        = ek ^ 2 * (2 - P.ρ) / (P.lam * (2 - P.ρ) ^ 2 * P.ρ * P.r) := by
      field_simp; ring
    have eR : (P.ρ - 1) / (P.lam * (2 - P.ρ) * P.ρ * P.r) * E ^ 2
        + P.ρ / (P.lam * (2 - P.ρ) ^ 2) / P.r * α ^ 2
        = ((P.ρ - 1) * (2 - P.ρ) * E ^ 2 + P.ρ ^ 2 * α ^ 2) / (P.lam * (2 - P.ρ) ^ 2 * P.ρ * P.r) := by
      field_simp
    rw [eL, eR]
    exact div_le_div_of_nonneg_right hsq (by positivity)

private lemma M_inner_nonneg {N : ℕ} (T : E N →L[ℝ] E N) (hT : T.IsPositive) (u : E N) :
    0 ≤ ⟪T u, u⟫ := by
  have := hT.inner_nonneg_left u
  simpa using this

private lemma M_inner_le {N : ℕ} (T : E N →L[ℝ] E N) (μ : ℝ) (hT : ‖T‖ ≤ μ) (u : E N) :
    ⟪T u, u⟫ ≤ μ * ‖u‖ ^ 2 := by
  calc ⟪T u, u⟫ ≤ ‖T u‖ * ‖u‖ := real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖u‖) * ‖u‖ := by gcongr; exact T.le_opNorm u
    _ ≤ (μ * ‖u‖) * ‖u‖ := by gcongr
    _ = μ * ‖u‖ ^ 2 := by ring

/-- Section 3 real value of `F_r` at `W k = (x_{k+1}, z_{k+1}, y_{k+1}, x_k, y_k)`. -/
private noncomputable def FR2 {n m : ℕ} (v : Variant) (P : Data n m)
    (x : ℕ → E n) (z y : ℕ → E m) (k : ℕ) : ℝ :=
  (P.g (z (k + 1))).toReal + R3 P (x (k + 1)) (z (k + 1)) (y (k + 1))
    + 2 * T1 P * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ ^ 2
    + C1 v P * ‖x (k + 1) - x k‖ ^ 2

private noncomputable def Wpt {n m : ℕ} (x : ℕ → E n) (z y : ℕ → E m) (k : ℕ) : Quint n m :=
  pack5 (x (k + 1)) (z (k + 1)) (y (k + 1)) (x k) (y k)

private lemma Freg_pack5 {n m : ℕ} (v : Variant) (P : Data n m)
    (X : E n) (Z Y : E m) (X' : E n) (Y' : E m) :
    BotNguyenADMM.Rates.Freg v P.g P.h P.A P.L P.r P.ρ P.lam P.μ₁ (pack5 X Z Y X' Y') =
      P.g Z + ((R3 P X Z Y
        + 2 * T1 P * ‖ContinuousLinearMap.adjoint P.A (Y - Y')‖ ^ 2
        + C1 v P * ‖X - X'‖ ^ 2 : ℝ) : EReal) := by
  unfold BotNguyenADMM.Rates.Freg BotNguyenADMM.Rates.augLag R3
  rw [add_assoc, ← EReal.coe_add]
  congr 2
  have hT1 : BotNguyenADMM.Rates.T1 P.lam P.ρ P.r = T1 P := rfl
  have hC1 : BotNguyenADMM.Rates.C1 v P.L P.μ₁ P.lam P.ρ P.r = C1 v P := by cases v <;> rfl
  rw [hT1, hC1]
  change P.h X + ⟪Y, P.A X - Z⟫ + P.r / 2 * ‖P.A X - Z‖ ^ 2 +
      (2 * T1 P * ‖ContinuousLinearMap.adjoint P.A (Y - Y')‖ ^ 2 + C1 v P * ‖X - X'‖ ^ 2) = _
  ring

private lemma Freg_Wpt {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    BotNguyenADMM.Rates.Freg v P.g P.h P.A P.L P.r P.ρ P.lam P.μ₁ (Wpt x z y k) =
      ((FR2 v P x z y k : ℝ) : EReal) := by
  unfold Wpt
  rw [Freg_pack5, gz_eq v P hA x z y hrun k, ← EReal.coe_add]
  congr 1
  unfold FR2
  ring

private lemma Fk_eq {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    BotNguyenADMM.Rates.Fk v P.g P.h P.A P.L P.r P.ρ P.lam P.μ₁ x z y (k + 1) =
      ((FR2 v P x z y k : ℝ) : EReal) := by
  unfold BotNguyenADMM.Rates.Fk
  simp only [Nat.add_sub_cancel]
  exact Freg_Wpt v P hA x z y hrun k

private lemma descent_key2 (τ kA kB c1 cMr α d0 d1 : ℝ) (hτ : 0 < τ) (hkB : 0 ≤ kB)
    (hα : 0 ≤ α) (hαle : α ≤ kA * d1 + kB * d0)
    (hC1 : c1 = 4 * kB ^ 2 * τ) (hCM : cMr = (8 * kA ^ 2 + 10 * kB ^ 2) * τ) :
    2 * τ * α ^ 2 + (c1 + τ * (if kB = 0 then kA ^ 2 else kB ^ 2)) * d1 ^ 2
      ≤ 1 / 2 * cMr * d1 ^ 2 + c1 * d0 ^ 2 := by
  subst hC1 hCM
  split_ifs with h0
  · subst h0
    have hα1 : α ≤ kA * d1 := by linarith
    have h2 : α ^ 2 ≤ (kA * d1) ^ 2 := pow_le_pow_left₀ hα hα1 2
    nlinarith
  · have h2 : α ^ 2 ≤ (kA * d1 + kB * d0) ^ 2 := pow_le_pow_left₀ hα hαle 2
    nlinarith [sq_nonneg (kA * d1 - kB * d0)]

private lemma descent_rates {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (h79 : ∀ k (w : E n),
      (P.L + BotNguyenADMM.Rates.CMprime v P.L P.μ₁ P.lam P.ρ / P.r) * ‖w‖ ^ 2 ≤
        2 * ⟪P.M₁ k w, w⟫ + P.r * ‖P.A w‖ ^ 2)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ k,
      FR2 v P x z y (k + 1)
        + κ * (‖x (k + 2) - x (k + 1)‖ ^ 2 + ‖y (k + 2) - y (k + 1)‖ ^ 2)
      ≤ FR2 v P x z y k := by
  have hT0 := T0_pos v P hA
  have hr := hA.r_pos
  have hL := L_pos v P hA
  have hμ := hA.μ₁_nonneg
  have hl := hA.lam_pos
  have hρ := hA.ρ_pos
  have hτ0 : 0 < T0 P / P.r := div_pos hT0 hr
  have hkB0 : 0 ≤ kapB v P := by cases v <;> simp [kapB] <;> linarith
  have hkAB : 0 < kapA v P + kapB v P := by cases v <;> simp [kapA, kapB] <;> linarith
  have hcpos : 0 < (if kapB v P = 0 then kapA v P ^ 2 else kapB v P ^ 2) := by
    split_ifs with h
    · have : 0 < kapA v P := by linarith
      positivity
    · exact pow_pos (lt_of_le_of_ne hkB0 (Ne.symm h)) 2
  set κx : ℝ := T0 P / P.r * (if kapB v P = 0 then kapA v P ^ 2 else kapB v P ^ 2) with hκxdef
  have hκx : 0 < κx := mul_pos hτ0 hcpos
  have hκy : 0 < 1 / (P.ρ * P.r) := by positivity
  refine ⟨min κx (1 / (P.ρ * P.r)), lt_min hκx hκy, fun k => ?_⟩
  have hz := z_step v P hA x z y hrun (k + 1) (z (k + 1)) _ (gz_eq v P hA x z y hrun k)
  have hPhi1 : Phi P (k + 1) (x (k + 1)) (z (k + 1)) (y (k + 1)) (z (k + 1))
      = ⟪y (k + 1), P.A (x (k + 1)) - z (k + 1)⟫ + P.r / 2 * ‖P.A (x (k + 1)) - z (k + 1)‖ ^ 2 := by
    unfold Phi; simp
  have hPhi2 : Phi P (k + 1) (x (k + 1)) (z (k + 1)) (y (k + 1)) (z (k + 1 + 1))
      = R3 P (x (k + 1)) (z (k + 1 + 1)) (y (k + 1)) - P.h (x (k + 1))
        + 1 / 2 * ⟪P.M₂ (k + 1) (z (k + 1 + 1) - z (k + 1)), z (k + 1 + 1) - z (k + 1)⟫ := by
    unfold Phi R3; ring
  rw [hPhi1, hPhi2] at hz
  have hM2 := M_inner_nonneg _ (hA.M₂_pos (k + 1)) (z (k + 1 + 1) - z (k + 1))
  have hx := x_step v P hA x z y hrun (k + 1)
  have hy := y_step v P hA x z y hrun (k + 1)
  have hm79 := h79 (k + 1) (x (k + 1 + 1) - x (k + 1))
  have hlam := hA.lam_le (y (k + 1 + 1) - y (k + 1))
  have hB := B_rec v P hA x z y hrun k
  have hdQ := dQ_bound v P hA x k
  have hek : ‖ContinuousLinearMap.adjoint P.A (y (k + 2) - y (k + 1))‖ ≤
      |1 - P.ρ| * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖
      + P.ρ * ‖(gxOf v P (x (k + 1)) (x (k + 2)) + P.M₁ (k + 1) (x (k + 2) - x (k + 1)))
        - (gxOf v P (x k) (x (k + 1)) + P.M₁ k (x (k + 1) - x k))‖ := by
    rw [hB]
    refine le_trans (norm_sub_le _ _) (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hρ]
  have hT := T_ineq v P hA _ _ _ (norm_nonneg _) hek
  have hdy : ‖y (k + 1 + 1) - y (k + 1)‖ ^ 2 / (P.ρ * P.r) ≤
      ‖ContinuousLinearMap.adjoint P.A (y (k + 2) - y (k + 1))‖ ^ 2 / (P.lam * P.ρ * P.r) := by
    have hρr : 0 < P.ρ * P.r := mul_pos hρ hr
    rw [div_le_div_iff₀ hρr (mul_pos (mul_pos hl hρ) hr)]
    nlinarith
  have key := descent_key2 (T0 P / P.r) (kapA v P) (kapB v P) (C1 v P)
    (BotNguyenADMM.Rates.CMprime v P.L P.μ₁ P.lam P.ρ / P.r) _ _ _ hτ0
    hkB0 (norm_nonneg _) hdQ
    (by rw [C1_eq]; ring) (by rw [CMprime_eq]; ring)
  have hstep : FR2 v P x z y (k + 1)
      + κx * ‖x (k + 2) - x (k + 1)‖ ^ 2
      + 1 / (P.ρ * P.r) * ‖y (k + 2) - y (k + 1)‖ ^ 2
      ≤ FR2 v P x z y k := by
    unfold FR2
    have hR3k : R3 P (x (k + 1)) (z (k + 1)) (y (k + 1)) = P.h (x (k + 1))
        + (⟪y (k + 1), P.A (x (k + 1)) - z (k + 1)⟫ + P.r / 2 * ‖P.A (x (k + 1)) - z (k + 1)‖ ^ 2) := by
      unfold R3; ring
    rw [hR3k]
    have e2 : k + 1 + 1 = k + 2 := rfl
    simp only [e2] at hz hx hy hm79 hM2 hdy ⊢
    have hdiv : 1 / (P.ρ * P.r) * ‖y (k + 2) - y (k + 1)‖ ^ 2 =
        ‖y (k + 2) - y (k + 1)‖ ^ 2 / (P.ρ * P.r) := by ring
    rw [hdiv]
    linarith [key]
  have hmin1 : min κx (1 / (P.ρ * P.r)) * ‖x (k + 2) - x (k + 1)‖ ^ 2 ≤
      κx * ‖x (k + 2) - x (k + 1)‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  have hmin2 : min κx (1 / (P.ρ * P.r)) * ‖y (k + 2) - y (k + 1)‖ ^ 2 ≤
      1 / (P.ρ * P.r) * ‖y (k + 2) - y (k + 1)‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
  linarith

private lemma pack5_sub {n m : ℕ} (a a' : E n) (b b' c c' : E m) (d d' : E n) (e e' : E m) :
    pack5 a b c d e - pack5 a' b' c' d' e' = pack5 (a - a') (b - b') (c - c') (d - d') (e - e') := by
  simp only [pack5, ← WithLp.toLp_sub, Prod.mk_sub_mk]

private lemma inner_pack5 {n m : ℕ} (a a' : E n) (b b' c c' : E m) (d d' : E n) (e e' : E m) :
    ⟪pack5 a b c d e, pack5 a' b' c' d' e'⟫ = ⟪a, a'⟫ + ⟪b, b'⟫ + ⟪c, c'⟫ + ⟪d, d'⟫ + ⟪e, e'⟫ := by
  simp [pack5, WithLp.prod_inner_apply]; ring

private lemma normsq_pack5 {n m : ℕ} (a : E n) (b c : E m) (d : E n) (e : E m) :
    ‖pack5 a b c d e‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 + ‖e‖ ^ 2 := by
  simp [pack5, WithLp.prod_norm_sq_eq_of_L2]; ring

private lemma pack5_eta {n m : ℕ} (u : Quint n m) :
    pack5 (qx u) (qz u) (qy u) (qx' u) (qy' u) = u := rfl

private lemma norm_pack5_le {n m : ℕ} (a : E n) (b c : E m) (d : E n) (e : E m) :
    ‖pack5 a b c d e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have h := normsq_pack5 a b c d e
  have h0 : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by positivity
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1 ?_
  rw [h]
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg d, norm_nonneg e,
    mul_nonneg (norm_nonneg a) (norm_nonneg b), mul_nonneg (norm_nonneg a) (norm_nonneg c),
    mul_nonneg (norm_nonneg a) (norm_nonneg d), mul_nonneg (norm_nonneg a) (norm_nonneg e),
    mul_nonneg (norm_nonneg b) (norm_nonneg c), mul_nonneg (norm_nonneg b) (norm_nonneg d),
    mul_nonneg (norm_nonneg b) (norm_nonneg e), mul_nonneg (norm_nonneg c) (norm_nonneg d),
    mul_nonneg (norm_nonneg c) (norm_nonneg e), mul_nonneg (norm_nonneg d) (norm_nonneg e)]

private lemma reg_of_quad {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (u V : X) (K : ℝ) (hK : 0 ≤ K) (hfin : f u ≠ ⊤)
    (hq : ∀ u', f u + ((⟪V, u' - u⟫ - K * ‖u' - u‖ ^ 2 : ℝ) : EReal) ≤ f u') :
    IsRegularSubgrad f u V := by
  refine ⟨hfin, fun ε hε => ?_⟩
  have hball : Metric.ball u (ε / (K + 1)) ∈ 𝓝 u := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  refine le_trans ?_ (hq w)
  have h1 : K * ‖w - u‖ ≤ ε := by
    have : ‖w - u‖ * (K + 1) < ε := (lt_div_iff₀ (by linarith)).1 hw
    nlinarith [norm_nonneg (w - u)]
  have h2 : ⟪V, w - u⟫ - ε * ‖w - u‖ ≤ ⟪V, w - u⟫ - K * ‖w - u‖ ^ 2 := by
    nlinarith [norm_nonneg (w - u)]
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.2 h2)

/-- The limiting subgradient of Section 3 `F_r` at `W k`. -/
private noncomputable def V2sub {n m : ℕ} (v : Variant) (P : Data n m)
    (x : ℕ → E n) (z y : ℕ → E m) (k : ℕ) : Quint n m :=
  pack5
    (gradient P.h (x (k + 1))
      + ContinuousLinearMap.adjoint P.A (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1)))
      + (2 * C1 v P) • (x (k + 1) - x k))
    ((y k + P.r • (P.A (x k) - z (k + 1)) - P.M₂ k (z (k + 1) - z k))
      - (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1))))
    ((P.A (x (k + 1)) - z (k + 1))
      + (4 * T1 P) • P.A (ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)))
    (-((2 * C1 v P) • (x (k + 1) - x k)))
    (-((4 * T1 P) • P.A (ContinuousLinearMap.adjoint P.A (y (k + 1) - y k))))

private lemma ereal_cases' (e : EReal) (he : e ≠ ⊥) : e = ⊤ ∨ ∃ r : ℝ, e = (r : EReal) := by
  by_cases h : e = ⊤
  · exact Or.inl h
  · exact Or.inr ⟨e.toReal, (EReal.coe_toReal h he).symm⟩

private lemma quad_bound (L a r μ dx dz dy dx' dy' : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hμ : 0 ≤ μ) :
    L / 2 * dx ^ 2 + dy * (a * dx + dz) + (r + μ) / 2 * dz ^ 2
      ≤ (L / 2 + a + 1 + (r + μ) / 2) * (dx ^ 2 + dz ^ 2 + dy ^ 2 + dx' ^ 2 + dy' ^ 2) := by
  nlinarith [sq_nonneg (dy - dx), sq_nonneg (dy - dz), mul_nonneg ha (sq_nonneg (dy - dx)),
    sq_nonneg dx', sq_nonneg dy', mul_nonneg hL (sq_nonneg dz), mul_nonneg hL (sq_nonneg dy),
    mul_nonneg ha (sq_nonneg dz), mul_nonneg (add_nonneg hr hμ) (sq_nonneg dx),
    mul_nonneg (add_nonneg hr hμ) (sq_nonneg dy), mul_nonneg hL (sq_nonneg dx'),
    mul_nonneg hL (sq_nonneg dy'), mul_nonneg ha (sq_nonneg dx'), mul_nonneg ha (sq_nonneg dy'),
    mul_nonneg (add_nonneg hr hμ) (sq_nonneg dx'), mul_nonneg (add_nonneg hr hμ) (sq_nonneg dy'),
    mul_nonneg ha (sq_nonneg dz), mul_nonneg ha (sq_nonneg dy)]

private lemma V2_minorant {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) (u' : Quint n m) :
    BotNguyenADMM.Rates.Freg v P.g P.h P.A P.L P.r P.ρ P.lam P.μ₁ (Wpt x z y k)
      + ((⟪V2sub v P x z y k, u' - Wpt x z y k⟫
      - (P.L / 2 + ‖P.A‖ + 1 + (P.r + P.μ₂) / 2) * ‖u' - Wpt x z y k‖ ^ 2 : ℝ) : EReal)
      ≤ BotNguyenADMM.Rates.Freg v P.g P.h P.A P.L P.r P.ρ P.lam P.μ₁ u' := by
  rw [← pack5_eta u']
  generalize qx u' = X
  generalize qz u' = Z
  generalize qy u' = Y
  generalize qx' u' = X'
  generalize qy' u' = Y'
  rw [Freg_Wpt v P hA x z y hrun k, Freg_pack5]
  rcases ereal_cases' (P.g Z) (hA.g_proper.1 Z) with h | ⟨gZ, hgZ⟩
  · rw [h, EReal.top_add_coe]; exact le_top
  rw [hgZ, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hz := z_step v P hA x z y hrun k Z gZ hgZ
  obtain ⟨DX, rfl⟩ : ∃ DX, X = x (k + 1) + DX := ⟨X - x (k + 1), by abel⟩
  obtain ⟨DZ, rfl⟩ : ∃ DZ, Z = z (k + 1) + DZ := ⟨Z - z (k + 1), by abel⟩
  obtain ⟨DY, rfl⟩ : ∃ DY, Y = y (k + 1) + DY := ⟨Y - y (k + 1), by abel⟩
  obtain ⟨DX', rfl⟩ : ∃ DX', X' = x k + DX' := ⟨X' - x k, by abel⟩
  obtain ⟨DY', rfl⟩ : ∃ DY', Y' = y k + DY' := ⟨Y' - y k, by abel⟩
  unfold Wpt
  rw [pack5_sub, normsq_pack5]
  simp only [add_sub_cancel_left]
  set p := P.A (x (k + 1)) - z (k + 1) with hp
  set q := P.A DX - DZ with hq
  set w := ContinuousLinearMap.adjoint P.A (y (k + 1) - y k) with hw
  set s := ContinuousLinearMap.adjoint P.A (DY - DY') with hs
  set Δ := x (k + 1) - x k with hΔ
  set p0 := P.A (x k) - z (k + 1) with hp0
  set a := z (k + 1) - z k with ha
  have hsymm : ∀ u u' : E m, ⟪P.M₂ k u, u'⟫ = ⟪u, P.M₂ k u'⟫ :=
    fun u u' => (hA.M₂_pos k).isSymmetric u u'
  have I1 : R3 P (x (k + 1) + DX) (z (k + 1) + DZ) (y (k + 1) + DY)
      = P.h (x (k + 1) + DX) + ⟪y (k + 1), p⟫ + ⟪y (k + 1), q⟫ + ⟪DY, p⟫ + ⟪DY, q⟫
        + P.r / 2 * (‖p‖ ^ 2 + 2 * ⟪p, q⟫ + ‖q‖ ^ 2) := by
    have e : P.A (x (k + 1) + DX) - (z (k + 1) + DZ) = p + q := by
      rw [hp, hq, map_add]; abel
    unfold R3; rw [e, norm_add_sq_real, inner_add_left, inner_add_right, inner_add_right]; ring
  have I2 : R3 P (x (k + 1)) (z (k + 1)) (y (k + 1)) = P.h (x (k + 1)) + ⟪y (k + 1), p⟫
      + P.r / 2 * ‖p‖ ^ 2 := rfl
  have I3 : ‖ContinuousLinearMap.adjoint P.A (y (k + 1) + DY - (y k + DY'))‖ ^ 2
      = ‖w‖ ^ 2 + 2 * (⟪P.A w, DY⟫ - ⟪P.A w, DY'⟫) + ‖s‖ ^ 2 := by
    have e : ContinuousLinearMap.adjoint P.A (y (k + 1) + DY - (y k + DY')) = w + s := by
      rw [hw, hs, ← map_add]; congr 1; abel
    rw [e, norm_add_sq_real, hs, ContinuousLinearMap.adjoint_inner_right, inner_sub_right]
  have I4 : ‖x (k + 1) + DX - (x k + DX')‖ ^ 2
      = ‖Δ‖ ^ 2 + 2 * (⟪Δ, DX⟫ - ⟪Δ, DX'⟫) + ‖DX - DX'‖ ^ 2 := by
    have e : x (k + 1) + DX - (x k + DX') = Δ + (DX - DX') := by rw [hΔ]; abel
    rw [e, norm_add_sq_real, inner_sub_right]
  have I5 : ⟪V2sub v P x z y k, pack5 DX DZ DY DX' DY'⟫
      = ⟪gradient P.h (x (k + 1)), DX⟫ + ⟪y (k + 1), q⟫ + P.r * ⟪p, q⟫ + 2 * C1 v P * ⟪Δ, DX⟫
        + (⟪y k, DZ⟫ + P.r * ⟪p0, DZ⟫ - ⟪P.M₂ k a, DZ⟫) + ⟪p, DY⟫ + 4 * T1 P * ⟪P.A w, DY⟫
        - 2 * C1 v P * ⟪Δ, DX'⟫ - 4 * T1 P * ⟪P.A w, DY'⟫ := by
    unfold V2sub
    simp only [← hp, ← hp0, ← ha, ← hw, ← hΔ]
    rw [inner_pack5]
    simp only [inner_add_left, inner_sub_left, inner_neg_left, real_inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left, hq, inner_sub_right]
    ring
  have I6 : Phi P k (x k) (z k) (y k) (z (k + 1) + DZ)
      = Phi P k (x k) (z k) (y k) (z (k + 1)) - ⟪y k, DZ⟫ - P.r * ⟪p0, DZ⟫ + P.r / 2 * ‖DZ‖ ^ 2
        + ⟪P.M₂ k a, DZ⟫ + 1 / 2 * ⟪P.M₂ k DZ, DZ⟫ := by
    have e1 : P.A (x k) - (z (k + 1) + DZ) = p0 - DZ := by rw [hp0]; abel
    have e2 : z (k + 1) + DZ - z k = a + DZ := by rw [ha]; abel
    have e3 : ⟪P.M₂ k (a + DZ), a + DZ⟫ = ⟪P.M₂ k a, a⟫ + 2 * ⟪P.M₂ k a, DZ⟫ + ⟪P.M₂ k DZ, DZ⟫ := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsymm DZ a,
        real_inner_comm (P.M₂ k a) DZ]
      ring
    unfold Phi
    rw [e1, e2, e3, ← hp0, ← ha, inner_sub_right, norm_sub_sq_real]
    ring
  have B1 := h_low v P hA (x (k + 1)) (x (k + 1) + DX)
  simp only [add_sub_cancel_left] at B1
  have hqn : ‖q‖ ≤ ‖P.A‖ * ‖DX‖ + ‖DZ‖ := by
    rw [hq]; exact le_trans (norm_sub_le _ _) (by gcongr; exact P.A.le_opNorm DX)
  have B2 : -(‖DY‖ * (‖P.A‖ * ‖DX‖ + ‖DZ‖)) ≤ ⟪DY, q⟫ := by
    have h1 := neg_le_of_abs_le (abs_real_inner_le_norm DY q)
    have h2 : ‖DY‖ * ‖q‖ ≤ ‖DY‖ * (‖P.A‖ * ‖DX‖ + ‖DZ‖) := by gcongr
    linarith
  have B3 := M_inner_le (P.M₂ k) P.μ₂ (hA.μ₂_bound k) DZ
  have hμ2 : 0 ≤ P.μ₂ := le_trans (norm_nonneg _) (hA.μ₂_bound k)
  have B5 := quad_bound P.L ‖P.A‖ P.r P.μ₂ ‖DX‖ ‖DZ‖ ‖DY‖ ‖DX'‖ ‖DY'‖ (L_pos v P hA).le
    (norm_nonneg _) hA.r_pos.le hμ2
  have B4a : 0 ≤ 2 * T1 P * ‖s‖ ^ 2 := mul_nonneg (mul_nonneg two_pos.le (T1_nonneg v P hA)) (sq_nonneg _)
  have B4b : 0 ≤ C1 v P * ‖DX - DX'‖ ^ 2 := mul_nonneg (C1_nonneg v P hA) (sq_nonneg _)
  have B4c : 0 ≤ P.r / 2 * ‖q‖ ^ 2 := mul_nonneg (div_nonneg hA.r_pos.le two_pos.le) (sq_nonneg _)
  rw [I6] at hz
  rw [I1, I3, I4, I5]
  unfold FR2
  rw [I2]
  simp only [← hw, ← hΔ]
  have hc1 := real_inner_comm DY p
  linarith [hz, B1, B2, B3, B5, B4a, B4b, B4c, hc1]

private lemma V2_reg {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    IsRegularSubgrad (BotNguyenADMM.Rates.Freg v P.g P.h P.A P.L P.r P.ρ P.lam P.μ₁)
      (Wpt x z y k) (V2sub v P x z y k) := by
  have hμ2 : 0 ≤ P.μ₂ := le_trans (norm_nonneg _) (hA.μ₂_bound 0)
  refine reg_of_quad _ _ _ (P.L / 2 + ‖P.A‖ + 1 + (P.r + P.μ₂) / 2)
    (by have := L_pos v P hA; have := hA.r_pos; positivity) ?_ (V2_minorant v P hA x z y hrun k)
  rw [Freg_Wpt v P hA x z y hrun k]; exact EReal.coe_ne_top _

private lemma V2_lim {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    V2sub v P x z y k ∈
      LimitingSubdiff (BotNguyenADMM.Rates.Freg v P.g P.h P.A P.L P.r P.ρ P.lam P.μ₁)
        (Wpt x z y k) := by
  refine ⟨(V2_reg v P hA x z y hrun k).1, fun _ => Wpt x z y k, fun _ => V2sub v P x z y k,
    tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds, fun _ => V2_reg v P hA x z y hrun k⟩

private lemma res_norm' {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    ‖P.A (x (k + 1)) - z (k + 1)‖ = ‖y (k + 1) - y k‖ / (P.ρ * P.r) := by
  have hpos : 0 < P.ρ * P.r := mul_pos hA.ρ_pos hA.r_pos
  rw [hy_rel hrun k, norm_smul, Real.norm_of_nonneg hpos.le, mul_div_cancel_left₀ _ hpos.ne']

private lemma dz_le {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    ‖z (k + 2) - z (k + 1)‖ ≤ ‖P.A‖ * ‖x (k + 2) - x (k + 1)‖
      + (‖y (k + 2) - y (k + 1)‖ + ‖y (k + 1) - y k‖) / (P.ρ * P.r) := by
  have e : z (k + 2) - z (k + 1) = P.A (x (k + 2) - x (k + 1))
      - ((P.A (x (k + 1 + 1)) - z (k + 1 + 1)) - (P.A (x (k + 1)) - z (k + 1))) := by
    rw [map_sub]; abel
  rw [e]
  have h1 := res_norm' v P hA x z y hrun (k + 1)
  have h2 := res_norm' v P hA x z y hrun k
  have h3 := norm_sub_le (P.A (x (k + 1 + 1)) - z (k + 1 + 1)) (P.A (x (k + 1)) - z (k + 1))
  have h4 := P.A.le_opNorm (x (k + 2) - x (k + 1))
  have h5 := norm_sub_le (P.A (x (k + 2) - x (k + 1)))
    ((P.A (x (k + 1 + 1)) - z (k + 1 + 1)) - (P.A (x (k + 1)) - z (k + 1)))
  rw [add_div]
  simp only [show k + 1 + 1 = k + 2 from rfl] at *
  linarith

private lemma V2_norm {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    ‖V2sub v P x z y k‖ ≤ (P.L + P.μ₁ + 4 * C1 v P + P.r * ‖P.A‖) * ‖x (k + 1) - x k‖
      + (1 + 8 * T1 P * ‖P.A‖) * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖
      + (1 + 1 / (P.ρ * P.r)) * ‖y (k + 1) - y k‖ + P.μ₂ * ‖z (k + 1) - z k‖ := by
  have hopt := xopt v P hA x z y hrun k
  have hC1 := C1_nonneg v P hA
  have hT1 := T1_nonneg v P hA
  have hr := hA.r_pos
  set Δ := x (k + 1) - x k with hΔ
  set w := ContinuousLinearMap.adjoint P.A (y (k + 1) - y k) with hw
  have hVx : gradient P.h (x (k + 1))
      + ContinuousLinearMap.adjoint P.A (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1)))
      + (2 * C1 v P) • Δ
      = (gradient P.h (x (k + 1)) - gxOf v P (x k) (x (k + 1))) + w - P.M₁ k Δ + (2 * C1 v P) • Δ := by
    have e : ContinuousLinearMap.adjoint P.A (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1)))
        = ContinuousLinearMap.adjoint P.A (y k + P.r • (P.A (x (k + 1)) - z (k + 1))) + w := by
      rw [hw, ← map_add]; congr 1; abel
    rw [e]
    have e2 : ContinuousLinearMap.adjoint P.A (y k + P.r • (P.A (x (k + 1)) - z (k + 1)))
        = -(gxOf v P (x k) (x (k + 1)) + P.M₁ k Δ) := by
      rw [eq_neg_iff_add_eq_zero, ← hopt]; abel
    rw [e2]; abel
  have hgx : ‖gradient P.h (x (k + 1)) - gxOf v P (x k) (x (k + 1))‖ ≤ P.L * ‖Δ‖ := by
    cases v with
    | prox => simp [gxOf]; exact mul_nonneg (L_pos _ P hA).le (norm_nonneg _)
    | linearized => simp only [gxOf]; exact hA.h_lip _ _
  have hM1 := M1_norm_le v P hA k Δ
  have hVxn : ‖(gradient P.h (x (k + 1)) - gxOf v P (x k) (x (k + 1))) + w - P.M₁ k Δ
      + (2 * C1 v P) • Δ‖ ≤ P.L * ‖Δ‖ + ‖w‖ + P.μ₁ * ‖Δ‖ + 2 * C1 v P * ‖Δ‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have := norm_sub_le ((gradient P.h (x (k + 1)) - gxOf v P (x k) (x (k + 1))) + w) (P.M₁ k Δ)
    have := norm_add_le (gradient P.h (x (k + 1)) - gxOf v P (x k) (x (k + 1))) w
    linarith
  have hVz : (y k + P.r • (P.A (x k) - z (k + 1)) - P.M₂ k (z (k + 1) - z k))
      - (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1)))
      = -(y (k + 1) - y k) - P.r • P.A Δ - P.M₂ k (z (k + 1) - z k) := by
    simp only [hΔ, map_sub, smul_sub]; abel
  have hM2 : ‖P.M₂ k (z (k + 1) - z k)‖ ≤ P.μ₂ * ‖z (k + 1) - z k‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hA.μ₂_bound k) (norm_nonneg _))
  have hAΔ : ‖P.A Δ‖ ≤ ‖P.A‖ * ‖Δ‖ := P.A.le_opNorm Δ
  have hAw : ‖P.A w‖ ≤ ‖P.A‖ * ‖w‖ := P.A.le_opNorm w
  have hVzn : ‖-(y (k + 1) - y k) - P.r • P.A Δ - P.M₂ k (z (k + 1) - z k)‖ ≤
      ‖y (k + 1) - y k‖ + P.r * (‖P.A‖ * ‖Δ‖) + P.μ₂ * ‖z (k + 1) - z k‖ := by
    have h1 := norm_sub_le (-(y (k + 1) - y k) - P.r • P.A Δ) (P.M₂ k (z (k + 1) - z k))
    have h2 := norm_sub_le (-(y (k + 1) - y k)) (P.r • P.A Δ)
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hr.le] at h2
    have h3 := mul_le_mul_of_nonneg_left hAΔ hr.le
    linarith
  have hVyn : ‖(P.A (x (k + 1)) - z (k + 1)) + (4 * T1 P) • P.A w‖ ≤
      ‖y (k + 1) - y k‖ / (P.ρ * P.r) + 4 * T1 P * (‖P.A‖ * ‖w‖) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [res_norm' v P hA x z y hrun k, norm_smul, Real.norm_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_left hAw (by positivity : (0 : ℝ) ≤ 4 * T1 P)
    linarith
  have hVan : ‖-((2 * C1 v P) • Δ)‖ = 2 * C1 v P * ‖Δ‖ := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hVbn : ‖-((4 * T1 P) • P.A w)‖ ≤ 4 * T1 P * (‖P.A‖ * ‖w‖) := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hAw (by positivity)
  have htot := norm_pack5_le
    (gradient P.h (x (k + 1))
      + ContinuousLinearMap.adjoint P.A (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1)))
      + (2 * C1 v P) • Δ)
    ((y k + P.r • (P.A (x k) - z (k + 1)) - P.M₂ k (z (k + 1) - z k))
      - (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1))))
    ((P.A (x (k + 1)) - z (k + 1)) + (4 * T1 P) • P.A w)
    (-((2 * C1 v P) • Δ)) (-((4 * T1 P) • P.A w))
  have hV : V2sub v P x z y k = pack5
    (gradient P.h (x (k + 1))
      + ContinuousLinearMap.adjoint P.A (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1)))
      + (2 * C1 v P) • Δ)
    ((y k + P.r • (P.A (x k) - z (k + 1)) - P.M₂ k (z (k + 1) - z k))
      - (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1))))
    ((P.A (x (k + 1)) - z (k + 1)) + (4 * T1 P) • P.A w)
    (-((2 * C1 v P) • Δ)) (-((4 * T1 P) • P.A w)) := rfl
  rw [hV]
  rw [hVx] at htot ⊢
  rw [hVz] at htot ⊢
  have hdiv : ‖y (k + 1) - y k‖ / (P.ρ * P.r) = 1 / (P.ρ * P.r) * ‖y (k + 1) - y k‖ := by ring
  rw [hdiv] at hVyn
  nlinarith [hVxn, hVzn, hVyn, hVan, hVbn, norm_nonneg w, norm_nonneg Δ, norm_nonneg P.A]

private lemma V2_bound {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) :
    ∃ M : ℝ, 0 < M ∧ ∀ j,
      ‖V2sub v P x z y (j + 1)‖ ≤
        M * (‖x (j + 2) - x (j + 1)‖ + ‖y (j + 2) - y (j + 1)‖ + ‖y (j + 1) - y j‖) := by
  have hC1 := C1_nonneg v P hA
  have hT1 := T1_nonneg v P hA
  have hr := hA.r_pos
  have hL := L_pos v P hA
  have hμ1 := hA.μ₁_nonneg
  have hμ2 : 0 ≤ P.μ₂ := le_trans (norm_nonneg _) (hA.μ₂_bound 0)
  have hρr : 0 < P.ρ * P.r := mul_pos hA.ρ_pos hr
  set c1 : ℝ := P.L + P.μ₁ + 4 * C1 v P + P.r * ‖P.A‖ + P.μ₂ * ‖P.A‖
  set c2 : ℝ := (1 + 8 * T1 P * ‖P.A‖) * ‖ContinuousLinearMap.adjoint P.A‖
      + (1 + 1 / (P.ρ * P.r)) + P.μ₂ / (P.ρ * P.r)
  set c3 : ℝ := P.μ₂ / (P.ρ * P.r)
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc3 : 0 ≤ c3 := by positivity
  refine ⟨1 + c1 + c2 + c3, by linarith, fun j => ?_⟩
  have hV := V2_norm v P hA x z y hrun (j + 1)
  have hdz := dz_le v P hA x z y hrun j
  simp only [show j + 1 + 1 = j + 2 from rfl] at hV
  have hAs : ‖ContinuousLinearMap.adjoint P.A (y (j + 2) - y (j + 1))‖ ≤
      ‖ContinuousLinearMap.adjoint P.A‖ * ‖y (j + 2) - y (j + 1)‖ :=
    (ContinuousLinearMap.adjoint P.A).le_opNorm _
  have hAs' := mul_le_mul_of_nonneg_left hAs (by positivity : (0 : ℝ) ≤ 1 + 8 * T1 P * ‖P.A‖)
  have hdz' := mul_le_mul_of_nonneg_left hdz hμ2
  have hlin : ‖V2sub v P x z y (j + 1)‖ ≤
      c1 * ‖x (j + 2) - x (j + 1)‖ + c2 * ‖y (j + 2) - y (j + 1)‖ + c3 * ‖y (j + 1) - y j‖ := by
    have hsplit : P.μ₂ * ((‖y (j + 2) - y (j + 1)‖ + ‖y (j + 1) - y j‖) / (P.ρ * P.r)) =
        P.μ₂ / (P.ρ * P.r) * ‖y (j + 2) - y (j + 1)‖ + P.μ₂ / (P.ρ * P.r) * ‖y (j + 1) - y j‖ := by
      ring
    linarith [hV, hAs', hdz', hsplit]
  have hd : 0 ≤ ‖x (j + 2) - x (j + 1)‖ := norm_nonneg _
  have hy1 : 0 ≤ ‖y (j + 2) - y (j + 1)‖ := norm_nonneg _
  have hy0 : 0 ≤ ‖y (j + 1) - y j‖ := norm_nonneg _
  nlinarith

private lemma sq_diff_le {N : ℕ} (u v : E N) : ‖u‖ ^ 2 - ‖v‖ ^ 2 ≤ ‖u - v‖ * (‖u‖ + ‖v‖) := by
  have h1 : ‖u‖ - ‖v‖ ≤ ‖u - v‖ := norm_sub_norm_le u v
  have h2 : 0 ≤ ‖u‖ + ‖v‖ := by positivity
  nlinarith

private lemma Phi_diff {n m : ℕ} (P : Data n m) (hμ : ∀ k, ‖P.M₂ k‖ ≤ P.μ₂) (hr : 0 ≤ P.r) (k : ℕ)
    (xk : E n) (zk yk a b : E m) :
    Phi P k xk zk yk a - Phi P k xk zk yk b ≤ (‖yk‖ + P.r / 2 * (‖P.A xk - a‖ + ‖P.A xk - b‖)
      + P.μ₂ / 2 * (‖a - zk‖ + ‖b - zk‖)) * ‖a - b‖ := by
  have hμ0 : 0 ≤ P.μ₂ := le_trans (norm_nonneg _) (hμ k)
  unfold Phi
  have t1 : ⟪yk, P.A xk - a⟫ - ⟪yk, P.A xk - b⟫ ≤ ‖yk‖ * ‖a - b‖ := by
    rw [← inner_sub_right]
    have e : P.A xk - a - (P.A xk - b) = -(a - b) := by abel
    rw [e, inner_neg_right]
    have := neg_le_of_abs_le (abs_real_inner_le_norm yk (a - b))
    linarith
  have t2 : ‖P.A xk - a‖ ^ 2 - ‖P.A xk - b‖ ^ 2 ≤ ‖a - b‖ * (‖P.A xk - a‖ + ‖P.A xk - b‖) := by
    have := sq_diff_le (P.A xk - a) (P.A xk - b)
    have e : P.A xk - a - (P.A xk - b) = -(a - b) := by abel
    rwa [e, norm_neg] at this
  have t3 : ⟪P.M₂ k (a - zk), a - zk⟫ - ⟪P.M₂ k (b - zk), b - zk⟫
      ≤ P.μ₂ * ‖a - b‖ * (‖a - zk‖ + ‖b - zk‖) := by
    have e : ⟪P.M₂ k (a - zk), a - zk⟫ - ⟪P.M₂ k (b - zk), b - zk⟫
        = ⟪P.M₂ k (a - b), a - zk⟫ + ⟪P.M₂ k (b - zk), a - b⟫ := by
      have gen : ∀ u w : E m, ⟪P.M₂ k u, u⟫ - ⟪P.M₂ k w, w⟫
          = ⟪P.M₂ k (u - w), u⟫ + ⟪P.M₂ k w, u - w⟫ := by
        intro u w; rw [map_sub, inner_sub_left, inner_sub_right]; ring
      have e1 : (a - zk) - (b - zk) = a - b := by abel
      rw [gen, e1]
    rw [e]
    have h1 : ⟪P.M₂ k (a - b), a - zk⟫ ≤ P.μ₂ * ‖a - b‖ * ‖a - zk‖ := by
      refine le_trans (real_inner_le_norm _ _) ?_
      have := (ContinuousLinearMap.le_opNorm (P.M₂ k) (a - b)).trans
        (mul_le_mul_of_nonneg_right (hμ k) (norm_nonneg _))
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have h2 : ⟪P.M₂ k (b - zk), a - b⟫ ≤ P.μ₂ * ‖a - b‖ * ‖b - zk‖ := by
      refine le_trans (real_inner_le_norm _ _) ?_
      have := (ContinuousLinearMap.le_opNorm (P.M₂ k) (b - zk)).trans
        (mul_le_mul_of_nonneg_right (hμ k) (norm_nonneg _))
      nlinarith [norm_nonneg (a - b)]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left t2 (by positivity : (0 : ℝ) ≤ P.r / 2)]

private lemma g_lim {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (R : ℝ)
    (hR : ∀ k, ‖x k‖ ≤ R ∧ ‖z k‖ ≤ R ∧ ‖y k‖ ≤ R)
    (zs : E m) (hzs : Tendsto (fun j => z (j + 1)) atTop (𝓝 zs)) :
    ∃ gs : ℝ, P.g zs = (gs : EReal) ∧
      Tendsto (fun j => (P.g (z (j + 1))).toReal) atTop (𝓝 gs) := by
  have hr := hA.r_pos
  have hμ0 : 0 ≤ P.μ₂ := le_trans (norm_nonneg _) (hA.μ₂_bound 0)
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR 0).1
  set C : ℝ → ℝ := fun t => R + P.r / 2 * (2 * (‖P.A‖ * R) + t + R) + P.μ₂ / 2 * (t + 3 * R)
    with hC
  have hC0 : ∀ t, 0 ≤ t → 0 ≤ C t := fun t ht => by rw [hC]; positivity
  have hPd : ∀ k (a : E m), Phi P k (x k) (z k) (y k) a - Phi P k (x k) (z k) (y k) (z (k + 1))
      ≤ C ‖a‖ * ‖a - z (k + 1)‖ := by
    intro k a
    refine le_trans (Phi_diff P hA.μ₂_bound hr.le k _ _ _ a (z (k + 1))) ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    obtain ⟨hx, hz, hy⟩ := hR k
    have hz1 := (hR (k + 1)).2.1
    have hAx : ‖P.A (x k)‖ ≤ ‖P.A‖ * R :=
      (P.A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    have n1 : ‖P.A (x k) - a‖ ≤ ‖P.A‖ * R + ‖a‖ := (norm_sub_le _ _).trans (by linarith)
    have n2 : ‖P.A (x k) - z (k + 1)‖ ≤ ‖P.A‖ * R + R := (norm_sub_le _ _).trans (by linarith)
    have n3 : ‖a - z k‖ ≤ ‖a‖ + R := (norm_sub_le _ _).trans (by linarith)
    have n4 : ‖z (k + 1) - z k‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
    rw [hC]
    have := mul_le_mul_of_nonneg_left (add_le_add n1 n2) (by positivity : (0 : ℝ) ≤ P.r / 2)
    have := mul_le_mul_of_nonneg_left (add_le_add n3 n4) (by positivity : (0 : ℝ) ≤ P.μ₂ / 2)
    nlinarith
  obtain ⟨w0, hw0⟩ := hA.g_proper.2
  have hg0 : P.g w0 = (((P.g w0).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hw0 (hA.g_proper.1 w0)).symm
  set U : ℝ := (P.g w0).toReal + C ‖w0‖ * (‖w0‖ + R) with hU
  have hup : ∀ k, (P.g (z (k + 1))).toReal ≤ U := by
    intro k
    have h1 := z_step v P hA x z y hrun k w0 _ hg0
    have h2 := hPd k w0
    have h3 : ‖w0 - z (k + 1)‖ ≤ ‖w0‖ + R := (norm_sub_le _ _).trans (by linarith [(hR (k + 1)).2.1])
    have h4 := mul_le_mul_of_nonneg_left h3 (hC0 _ (norm_nonneg w0))
    rw [hU]; linarith
  have hle : P.g zs ≤ (U : EReal) := by
    by_contra hcon
    push Not at hcon
    have hev := hzs.eventually (hA.g_lsc zs (U : EReal) hcon)
    obtain ⟨j, hj⟩ := hev.exists
    rw [gz_eq v P hA x z y hrun j] at hj
    have := hup j
    have : (U : ℝ) < (P.g (z (j + 1))).toReal := by exact_mod_cast hj
    linarith
  have hne : P.g zs ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top U) hle
  refine ⟨(P.g zs).toReal, (EReal.coe_toReal hne (hA.g_proper.1 zs)).symm, ?_⟩
  set gs := (P.g zs).toReal with hgs
  have hgs' : P.g zs = (gs : EReal) := (EReal.coe_toReal hne (hA.g_proper.1 zs)).symm
  rw [tendsto_order]
  constructor
  · intro c hc
    have hc' : (c : EReal) < P.g zs := by rw [hgs']; exact_mod_cast hc
    filter_upwards [hzs.eventually (hA.g_lsc zs (c : EReal) hc')] with j hj
    rw [gz_eq v P hA x z y hrun j] at hj
    exact_mod_cast hj
  · intro c hc
    have hdist : Tendsto (fun j => C ‖zs‖ * ‖zs - z (j + 1)‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j => ‖z (j + 1) - zs‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.1 hzs
      have h2 := h1.const_mul (C ‖zs‖)
      rw [mul_zero] at h2
      refine h2.congr (fun j => ?_)
      rw [norm_sub_rev]
    filter_upwards [hdist.eventually (gt_mem_nhds (show (0 : ℝ) < c - gs by linarith))] with j hj
    have h1 := z_step v P hA x z y hrun j zs gs hgs'
    have h2 := hPd j zs
    linarith

private lemma assumption1_of_assumption2 {n m : ℕ} (v : Variant)
    (g : E m → EReal) (h : E n → ℝ) (A : E n →L[ℝ] E m)
    (L r ρ lam μ₁ μ₂ : ℝ) (M₁ : ℕ → E n →L[ℝ] E n) (M₂ : ℕ → E m →L[ℝ] E m)
    (hA2 : BotNguyenADMM.Rates.Assumption2 v g h A L r ρ lam μ₁ μ₂ M₁ M₂) :
    Assumption1 v ⟨g, h, A, L, r, ρ, M₁, M₂, lam, μ₁, μ₂⟩ := by
  refine
    { g_proper := hA2.g_proper
      g_lsc := hA2.g_lsc
      h_diff := hA2.h_diff
      h_lip := hA2.h_lipschitz
      M₁_pos := hA2.M₁_psd
      M₂_pos := hA2.M₂_psd
      r_pos := hA2.r_pos
      ρ_pos := hA2.ρ_pos
      ρ_lt := hA2.ρ_lt_two
      g_bdd := hA2.g_bdd_below
      h_bdd := hA2.h_bdd_below
      lam_pos := hA2.lam_pos
      lam_le := hA2.lam_le
      μ₁_bound := hA2.M₁_bdd
      μ₂_bound := hA2.M₂_bdd
      μ₁_nonneg := hA2.μ₁_nonneg
      eq14 := ⟨hA2.r_ge, hA2.L_pos⟩
      eq15 := ?_ }
  intro k w
  refine le_trans ?_ (hA2.metric_79 k w)
  have hT0 : 0 < BotNguyenADMM.Rates.T0 lam ρ := by
    have hl := hA2.lam_pos; have h0 := hA2.ρ_pos; have h2 := hA2.ρ_lt_two
    unfold BotNguyenADMM.Rates.T0; split_ifs
    · positivity
    · have : 0 < 2 - ρ := by linarith
      positivity
  have hCM : CM v ⟨g, h, A, L, r, ρ, M₁, M₂, lam, μ₁, μ₂⟩ ≤
      BotNguyenADMM.Rates.CMprime v L μ₁ lam ρ := by
    cases v <;>
      simp only [CM, BotNguyenADMM.Rates.CMprime] <;>
      change _ * BotNguyenADMM.Rates.T0 lam ρ ≤ _ * BotNguyenADMM.Rates.T0 lam ρ <;>
      nlinarith [sq_nonneg μ₁, sq_nonneg (L + μ₁)]
  have hdiv : CM v ⟨g, h, A, L, r, ρ, M₁, M₂, lam, μ₁, μ₂⟩ / r ≤
      BotNguyenADMM.Rates.CMprime v L μ₁ lam ρ / r :=
    div_le_div_of_nonneg_right hCM hA2.r_pos.le
  nlinarith [sq_nonneg ‖w‖]

end Helpers

open Filter Topology NonconvexSplitting.Shared BotNguyenADMM.Rates in
open scoped InnerProductSpace RealInnerProductSpace in
theorem solution
    {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (g : BotNguyenADMM.KL.E m → EReal) (h : BotNguyenADMM.KL.E n → ℝ) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m)
    (L r ρ lam μ₁ μ₂ : ℝ) (M₁ : ℕ → BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E n) (M₂ : ℕ → BotNguyenADMM.KL.E m →L[ℝ] BotNguyenADMM.KL.E m)
    (hA2 : Assumption2 v g h A L r ρ lam μ₁ μ₂ M₁ M₂)
    (x : ℕ → BotNguyenADMM.KL.E n) (z y : ℕ → BotNguyenADMM.KL.E m) (hrun : IsRun v g h A r ρ M₁ M₂ x z y)
    (hbx : Bornology.IsBounded (Set.range x)) (hbz : Bornology.IsBounded (Set.range z))
    (hby : Bornology.IsBounded (Set.range y))
    (xh : BotNguyenADMM.KL.E n) (zh yh : BotNguyenADMM.KL.E m) (CL θ : ℝ)
    (hloj : LojAt v g h A L r ρ lam μ₁ x z y xh zh yh CL θ) :
    (θ = 0 → ∃ K : ℕ, 1 ≤ K ∧ ∀ k ≥ K,
      Fk v g h A L r ρ lam μ₁ x z y k = Fstar v g h A L r ρ lam μ₁ xh zh yh) ∧
    (0 < θ ∧ θ ≤ 1 / 2 → ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∃ C0hat : ℝ, 0 < C0hat ∧ ∃ Q : ℝ, 0 ≤ Q ∧ Q < 1 ∧
      ∀ k ≥ k₀, 0 ≤ Ek v g h A L r ρ lam μ₁ x z y xh zh yh k ∧
        Ek v g h A L r ρ lam μ₁ x z y xh zh yh k ≤ C0hat * Q ^ k) ∧
    (1 / 2 < θ ∧ θ < 1 → ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∃ C1hat : ℝ, 0 < C1hat ∧
      ∀ k ≥ k₀, 0 ≤ Ek v g h A L r ρ lam μ₁ x z y xh zh yh k ∧
        Ek v g h A L r ρ lam μ₁ x z y xh zh yh k ≤
          C1hat * ((k : ℝ) - 1) ^ (-(1 / (2 * θ - 1)))) := by
  let P : BotNguyenADMM.KL.Data n m := ⟨g, h, A, L, r, ρ, M₁, M₂, lam, μ₁, μ₂⟩
  have hA1 : BotNguyenADMM.KL.Assumption1 v P :=
    assumption1_of_assumption2 v g h A L r ρ lam μ₁ μ₂ M₁ M₂ hA2
  have hrunP : BotNguyenADMM.KL.IsRun v P x z y := hrun
  obtain ⟨hCL, hθ0, hθ1, hxh, hzh, hyh, ε, hε, hLojBall⟩ := hloj
  -- Common norm bound R on the iterates
  obtain ⟨Rx, hRx⟩ := isBounded_iff_forall_norm_le.1 hbx
  obtain ⟨Rz, hRz⟩ := isBounded_iff_forall_norm_le.1 hbz
  obtain ⟨Ry, hRy⟩ := isBounded_iff_forall_norm_le.1 hby
  set R : ℝ := max Rx (max Rz Ry)
  have hR : ∀ k, ‖x k‖ ≤ R ∧ ‖z k‖ ≤ R ∧ ‖y k‖ ≤ R := fun k =>
    ⟨(hRx _ ⟨k, rfl⟩).trans (le_max_left _ _),
     (hRz _ ⟨k, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _)),
     (hRy _ ⟨k, rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  -- Descent inequality for FR2
  obtain ⟨κ, hκ, hdec⟩ := descent_rates v P hA1 hA2.metric_79 x z y hrunP
  -- Convergence of g(z_{k+1}) to g(zh) and of FR2 k to Fs = Fstar.toReal
  have hx1 : Tendsto (fun j => x (j + 1)) atTop (𝓝 xh) := hxh.comp (tendsto_add_atTop_nat 1)
  have hz1 : Tendsto (fun j => z (j + 1)) atTop (𝓝 zh) := hzh.comp (tendsto_add_atTop_nat 1)
  have hy1 : Tendsto (fun j => y (j + 1)) atTop (𝓝 yh) := hyh.comp (tendsto_add_atTop_nat 1)
  obtain ⟨gs, hgs, hgt⟩ := g_lim v P hA1 x z y hrunP R hR zh hz1
  set Fs : ℝ := gs + R3 P xh zh yh with hFsdef
  have hFstar_eq : Fstar v g h A L r ρ lam μ₁ xh zh yh = (Fs : EReal) := by
    unfold Fstar
    change BotNguyenADMM.Rates.Freg v P.g P.h P.A P.L P.r P.ρ P.lam P.μ₁
      (BotNguyenADMM.KL.pack5 xh zh yh xh yh) = _
    rw [Freg_pack5, hgs, ← EReal.coe_add]
    congr 1
    simp [hFsdef]
  have hFstar_toReal : (Fstar v g h A L r ρ lam μ₁ xh zh yh).toReal = Fs := by
    rw [hFstar_eq, EReal.toReal_coe]
  have hFR2_lim : Tendsto (FR2 v P x z y) atTop (𝓝 Fs) := by
    have hAx : Tendsto (fun j => A (x (j + 1)) - z (j + 1)) atTop (𝓝 (A xh - zh)) :=
      ((A.continuous.tendsto _).comp hx1).sub hz1
    have hR3 : Tendsto (fun j => R3 P (x (j + 1)) (z (j + 1)) (y (j + 1))) atTop (𝓝 (R3 P xh zh yh)) :=
      (((hA2.h_diff.continuous.tendsto _).comp hx1).add (hy1.inner hAx)).add
        ((hAx.norm.pow 2).const_mul _)
    have hT : Tendsto (fun j => 2 * BotNguyenADMM.KL.T1 P *
        ‖ContinuousLinearMap.adjoint A (y (j + 1) - y j)‖ ^ 2) atTop (𝓝 0) := by
      have h1 := (((((ContinuousLinearMap.adjoint A).continuous.tendsto _).comp
        (hy1.sub hyh)).norm).pow 2).const_mul (2 * BotNguyenADMM.KL.T1 P)
      simpa using h1
    have hC : Tendsto (fun j => BotNguyenADMM.KL.C1 v P * ‖x (j + 1) - x j‖ ^ 2) atTop (𝓝 0) := by
      have h1 := (((hx1.sub hxh).norm).pow 2).const_mul (BotNguyenADMM.KL.C1 v P)
      simpa using h1
    have hsum := ((hgt.add hR3).add hT).add hC
    rw [add_zero, add_zero] at hsum
    exact hsum
  -- Monotonicity and nonnegativity of FR2 - Fs
  have hFR2_anti : Antitone (FR2 v P x z y) := antitone_nat_of_succ_le (fun j => by
    have := hdec j
    have hnn : 0 ≤ κ * (‖x (j + 2) - x (j + 1)‖ ^ 2 + ‖y (j + 2) - y (j + 1)‖ ^ 2) := by positivity
    linarith)
  have hFR2_ge : ∀ j, Fs ≤ FR2 v P x z y j := fun j => le_of_tendsto hFR2_lim
    (eventually_atTop.2 ⟨j, fun m hm => hFR2_anti hm⟩)
  -- Express Ek (j + 1) in terms of FR2 j
  have hEk_succ : ∀ j, Ek v g h A L r ρ lam μ₁ x z y xh zh yh (j + 1) = FR2 v P x z y j - Fs := by
    intro j
    unfold Ek
    rw [Fk_eq v P hA1 x z y hrunP j, EReal.toReal_coe, hFstar_toReal]
  -- Define e : ℕ → ℝ matching Ek for k ≥ 1 and constant at 0
  set e : ℕ → ℝ := fun k =>
    if k = 0 then Ek v g h A L r ρ lam μ₁ x z y xh zh yh 1
    else Ek v g h A L r ρ lam μ₁ x z y xh zh yh k with hedef
  have he_pos_eq : ∀ k, 1 ≤ k → e k = Ek v g h A L r ρ lam μ₁ x z y xh zh yh k := fun k hk => by
    simp [hedef, show k ≠ 0 by omega]
  have he_succ : ∀ j, e (j + 1) = FR2 v P x z y j - Fs := fun j => by
    rw [he_pos_eq (j + 1) (by omega), hEk_succ j]
  have he_nonneg : ∀ k, 0 ≤ e k := by
    intro k
    cases k with
    | zero =>
      simp only [hedef, ↓reduceIte, hEk_succ 0]
      linarith [hFR2_ge 0]
    | succ j =>
      rw [he_succ j]
      linarith [hFR2_ge j]
  have he_anti : Antitone e := antitone_nat_of_succ_le (fun k => by
    cases k with
    | zero =>
      simp only [hedef, ↓reduceIte, one_ne_zero, zero_add, le_refl]
    | succ j =>
      rw [he_succ (j + 1), he_succ j]
      linarith [hFR2_anti (Nat.le_succ j)])
  have he_lim : Tendsto e atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have h1 : Tendsto (fun j => FR2 v P x z y j - Fs) atTop (𝓝 (Fs - Fs)) :=
      hFR2_lim.sub tendsto_const_nhds
    rw [sub_self] at h1
    exact h1.congr (fun j => (he_succ j).symm)
  -- Eventual membership of Wpt k in the Łojasiewicz ball
  have hW_ball : ∀ᶠ j in atTop,
      Wpt x z y j ∈ Metric.ball (pack5 xh zh yh xh yh) ε := by
    have hd : Tendsto (fun j => ‖x (j + 1) - xh‖ + ‖z (j + 1) - zh‖ + ‖y (j + 1) - yh‖
        + ‖x j - xh‖ + ‖y j - yh‖) atTop (𝓝 0) := by
      have t1 := tendsto_iff_norm_sub_tendsto_zero.1 hx1
      have t2 := tendsto_iff_norm_sub_tendsto_zero.1 hz1
      have t3 := tendsto_iff_norm_sub_tendsto_zero.1 hy1
      have t4 := tendsto_iff_norm_sub_tendsto_zero.1 hxh
      have t5 := tendsto_iff_norm_sub_tendsto_zero.1 hyh
      simpa using (((t1.add t2).add t3).add t4).add t5
    filter_upwards [hd.eventually (gt_mem_nhds hε)] with j hj
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : Wpt x z y j - pack5 xh zh yh xh yh =
        BotNguyenADMM.KL.pack5 (x (j + 1) - xh) (z (j + 1) - zh) (y (j + 1) - yh)
          (x j - xh) (y j - yh) :=
      pack5_sub _ _ _ _ _ _ _ _ _ _
    rw [hsub]
    exact lt_of_le_of_lt (norm_pack5_le _ _ _ _ _) hj
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hW_ball
  -- Subgradient norm bound and recurrence with l₀ = 2
  obtain ⟨M, hM, hVb⟩ := V2_bound v P hA1 x z y hrunP
  set k0 : ℕ := N0 + 3 with hk0def
  set Ce : ℝ := κ / (3 * CL ^ 2 * M ^ 2) with hCedef
  have hCe : 0 < Ce := by positivity
  have h71 : ∀ k ≥ k0, Ce * (if e k = 0 then 0 else e k ^ (2 * θ)) ≤ e (k - 2) - e k := by
    intro k hk
    by_cases he0 : e k = 0
    · rw [if_pos he0, mul_zero]
      have := he_anti (show k - 2 ≤ k by omega)
      linarith
    · rw [if_neg he0]
      set j : ℕ := k - 2 with hjdef
      have hk_eq : k = j + 2 := by omega
      have hj_ge : N0 + 1 ≤ j := by omega
      have he_pos : 0 < e k := lt_of_le_of_ne (he_nonneg k) (Ne.symm he0)
      have hek_val : e k = FR2 v P x z y (j + 1) - Fs := by
        rw [hk_eq, he_succ (j + 1)]
      have hek2_val : e (k - 2) = FR2 v P x z y (j - 1) - Fs := by
        have hk2 : k - 2 = (j - 1) + 1 := by omega
        rw [hk2, he_succ (j - 1)]
      have hW_mem : Wpt x z y (j + 1) ∈ Metric.ball (pack5 xh zh yh xh yh) ε :=
        hN0 (j + 1) (by omega)
      have hF_eq : Freg v g h A L r ρ lam μ₁ (Wpt x z y (j + 1)) =
          ((FR2 v P x z y (j + 1) : ℝ) : EReal) :=
        Freg_Wpt v P hA1 x z y hrunP (j + 1)
      have hF_ne : Freg v g h A L r ρ lam μ₁ (Wpt x z y (j + 1)) ≠
          Fstar v g h A L r ρ lam μ₁ xh zh yh := by
        rw [hF_eq, hFstar_eq]
        intro hEq
        have hEq' : FR2 v P x z y (j + 1) = Fs := by exact_mod_cast hEq
        linarith [hek_val, he_pos]
      have hLoj := hLojBall (Wpt x z y (j + 1)) hW_mem (V2sub v P x z y (j + 1))
        (V2_lim v P hA1 x z y hrunP (j + 1)) hF_ne
      rw [hF_eq, EReal.toReal_coe, hFstar_toReal, ← hek_val, abs_of_pos he_pos] at hLoj
      have hVn : ‖V2sub v P x z y (j + 1)‖ ≤
          M * (‖x (j + 2) - x (j + 1)‖ + ‖y (j + 2) - y (j + 1)‖ + ‖y (j + 1) - y j‖) :=
        hVb j
      have hLoj' : e k ^ θ ≤
          CL * M * (‖x (j + 2) - x (j + 1)‖ + ‖y (j + 2) - y (j + 1)‖ + ‖y (j + 1) - y j‖) := by
        have := mul_le_mul_of_nonneg_left hVn hCL.le
        linarith
      have hsq1 : e k ^ (2 * θ) ≤
          (CL * M * (‖x (j + 2) - x (j + 1)‖ + ‖y (j + 2) - y (j + 1)‖ + ‖y (j + 1) - y j‖)) ^ 2 := by
        have hpow : e k ^ (2 * θ) = (e k ^ θ) ^ 2 := by
          rw [mul_comm, Real.rpow_mul he_pos.le, Real.rpow_two]
        rw [hpow]
        exact pow_le_pow_left₀ (Real.rpow_nonneg he_pos.le θ) hLoj' 2
      have hcs : (‖x (j + 2) - x (j + 1)‖ + ‖y (j + 2) - y (j + 1)‖ + ‖y (j + 1) - y j‖) ^ 2 ≤
          3 * (‖x (j + 2) - x (j + 1)‖ ^ 2 + ‖y (j + 2) - y (j + 1)‖ ^ 2 + ‖y (j + 1) - y j‖ ^ 2) := by
        nlinarith [sq_nonneg (‖x (j + 2) - x (j + 1)‖ - ‖y (j + 2) - y (j + 1)‖),
          sq_nonneg (‖x (j + 2) - x (j + 1)‖ - ‖y (j + 1) - y j‖),
          sq_nonneg (‖y (j + 2) - y (j + 1)‖ - ‖y (j + 1) - y j‖)]
      have hsq2 : e k ^ (2 * θ) ≤
          3 * CL ^ 2 * M ^ 2 *
            (‖x (j + 2) - x (j + 1)‖ ^ 2 + ‖y (j + 2) - y (j + 1)‖ ^ 2 + ‖y (j + 1) - y j‖ ^ 2) := by
        have hcm : 0 ≤ (CL * M) ^ 2 := sq_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hcs hcm
        nlinarith
      have hdec1 := hdec j
      have hdec0 := hdec (j - 1)
      have hj1 : j - 1 + 1 = j := by omega
      have hj2 : j - 1 + 2 = j + 1 := by omega
      rw [hj1, hj2] at hdec0
      have hdec_sum : κ * (‖x (j + 2) - x (j + 1)‖ ^ 2 + ‖y (j + 2) - y (j + 1)‖ ^ 2
          + ‖y (j + 1) - y j‖ ^ 2) ≤ FR2 v P x z y (j - 1) - FR2 v P x z y (j + 1) := by
        have hx0 : 0 ≤ κ * ‖x (j + 1) - x j‖ ^ 2 := by positivity
        linarith
      have hden : 0 < 3 * CL ^ 2 * M ^ 2 := by positivity
      have hstep : Ce * e k ^ (2 * θ) ≤
          κ * (‖x (j + 2) - x (j + 1)‖ ^ 2 + ‖y (j + 2) - y (j + 1)‖ ^ 2 + ‖y (j + 1) - y j‖ ^ 2) := by
        rw [hCedef, div_mul_eq_mul_div, div_le_iff₀ hden]
        nlinarith
      have hfinal : Ce * e k ^ (2 * θ) ≤ FR2 v P x z y (j - 1) - FR2 v P x z y (j + 1) :=
        hstep.trans hdec_sum
      linarith [hfinal, hek_val, hek2_val]
  -- Apply Lemma 15 with l₀ = 2
  obtain ⟨hres1, hres2, hres3⟩ :=
    BotNguyenADMM.Rates.lemma_15 e he_nonneg he_anti he_lim k0 2 (by omega) (by omega)
      Ce θ hCe hθ0 hθ1 h71
  refine ⟨?_, ?_, ?_⟩
  · intro hθ
    obtain ⟨K, hK⟩ := hres1 hθ
    refine ⟨max K 1, le_max_right _ _, fun k hk => ?_⟩
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
    have hkK : K ≤ k := le_trans (le_max_left _ _) hk
    have he0 : Ek v g h A L r ρ lam μ₁ x z y xh zh yh k = 0 := by
      rw [← he_pos_eq k hk1]; exact hK k hkK
    have hk_eq : k = (k - 1) + 1 := by omega
    rw [hk_eq, Fk_eq v P hA1 x z y hrunP (k - 1), hFstar_eq]
    rw [hk_eq, hEk_succ (k - 1)] at he0
    congr 1
    linarith
  · intro hθ
    obtain ⟨Ce0, hCe0, Q, hQ0, hQ1, hbound⟩ := hres2 hθ
    refine ⟨k0, by omega, Ce0, hCe0, Q, hQ0, hQ1, fun k hk => ?_⟩
    have hk1 : 1 ≤ k := by omega
    rw [← he_pos_eq k hk1]
    exact hbound k hk
  · intro hθ
    obtain ⟨Ce1, hCe1, hbound⟩ := hres3 hθ
    refine ⟨k0 + 2, by omega, Ce1, hCe1, fun k hk => ?_⟩
    have hk1 : 1 ≤ k := by omega
    rw [← he_pos_eq k hk1]
    have hb := hbound k hk
    have harg : ((k : ℝ) - (2 : ℕ) + 1) = (k : ℝ) - 1 := by norm_num; ring
    rwa [harg] at hb
