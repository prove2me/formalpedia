-- Prove2me | solution 1 for BotNguyenADMM.KL.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T12:11:36.900998+00:00
-- url     : https://prove2.me/submissions/620444b4-ecf8-49b2-817e-c20836ce99a2

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_BotNguyenADMM_KL_Setting
open NonconvexSplitting.Shared BotNguyenADMM.KL
open Filter Topology
open scoped RealInnerProductSpace

set_option autoImplicit false

noncomputable def hpOf {n m : ℕ} (v : Variant) (P : Data n m) (xk u : E n) : ℝ :=
  match v with
  | .prox => P.h u
  | .linearized => ⟪u - xk, gradient P.h xk⟫

noncomputable def gxOf {n m : ℕ} (v : Variant) (P : Data n m) (xk xk1 : E n) : E n :=
  match v with
  | .prox => gradient P.h xk1
  | .linearized => gradient P.h xk

theorem xObj_eq' {n m : ℕ} (v : Variant) (P : Data n m) (k : ℕ) (xk : E n) (zk1 yk : E m) (u : E n) :
    xObj v P k xk zk1 yk u = hpOf v P xk u + ⟪yk, P.A u - zk1⟫ + P.r / 2 * ‖P.A u - zk1‖ ^ 2
      + 1 / 2 * ⟪P.M₁ k (u - xk), u - xk⟫ := by
  cases v <;> rfl

theorem hpOf_deriv {n m : ℕ} (v : Variant) (P : Data n m) (hd : Differentiable ℝ P.h)
    (xk u0 d : E n) :
    HasDerivAt (fun t : ℝ => hpOf v P xk (u0 + t • d)) ⟪gxOf v P xk u0, d⟫ 0 := by
  have hℓ : HasDerivAt (fun t : ℝ => u0 + t • d) d 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const d).const_add u0
    simpa using this
  cases v with
  | prox =>
    have hd' : HasFDerivAt P.h (fderiv ℝ P.h (u0 + (0:ℝ) • d)) (u0 + (0:ℝ) • d) :=
      (hd _).hasFDerivAt
    have := hd'.comp_hasDerivAt (0:ℝ) hℓ
    have e : fderiv ℝ P.h u0 d = ⟪gradient P.h u0, d⟫ := by
      unfold gradient
      rw [InnerProductSpace.toDual_symm_apply]
    simp only [zero_smul, add_zero] at this
    rw [e] at this
    exact this
  | linearized =>
    have h1 : HasDerivAt (fun t : ℝ => u0 + t • d - xk) d 0 := hℓ.sub_const xk
    have h2 := h1.inner ℝ (hasDerivAt_const (0:ℝ) (gradient P.h xk))
    simpa [hpOf, gxOf] using h2

theorem xopt {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    gxOf v P (x k) (x (k + 1))
      + ContinuousLinearMap.adjoint P.A (y k + P.r • (P.A (x (k + 1)) - z (k + 1)))
      + P.M₁ k (x (k + 1) - x k) = 0 := by
  obtain ⟨_, hxmin, _⟩ := hrun k
  set u0 := x (k + 1) with hu0
  set G : E n := gxOf v P (x k) u0
      + ContinuousLinearMap.adjoint P.A (y k + P.r • (P.A u0 - z (k + 1)))
      + P.M₁ k (u0 - x k) with hG
  have hsymm : ∀ a b : E n, ⟪P.M₁ k a, b⟫ = ⟪a, P.M₁ k b⟫ := fun a b => (hA.M₁_pos k).isSymmetric a b
  have key : ∀ d : E n, ⟪G, d⟫ = 0 := by
    intro d
    have hℓ : HasDerivAt (fun t : ℝ => u0 + t • d) d 0 := by
      have := ((hasDerivAt_id (0:ℝ)).smul_const d).const_add u0
      simpa using this
    have hmin : IsLocalMin (fun t : ℝ => xObj v P k (x k) (z (k + 1)) (y k) (u0 + t • d)) 0 := by
      refine Filter.Eventually.of_forall (fun t => ?_)
      have := hxmin (u0 + t • d)
      simpa using this
    have hAℓ : HasDerivAt (fun t : ℝ => P.A (u0 + t • d) - z (k + 1)) (P.A d) 0 := by
      have := P.A.hasFDerivAt.comp_hasDerivAt (0:ℝ) hℓ
      exact this.sub_const (z (k + 1))
    have hq : HasDerivAt (fun t : ℝ => ‖P.A (u0 + t • d) - z (k + 1)‖ ^ 2)
        (2 * ⟪P.A u0 - z (k + 1), P.A d⟫) 0 := by
      have := hAℓ.norm_sq
      simpa using this
    have hin : HasDerivAt (fun t : ℝ => ⟪y k, P.A (u0 + t • d) - z (k + 1)⟫) ⟪y k, P.A d⟫ 0 := by
      have := (hasDerivAt_const (0:ℝ) (y k)).inner ℝ hAℓ
      simpa using this
    have hℓ' : HasDerivAt (fun t : ℝ => u0 + t • d - x k) d 0 := hℓ.sub_const (x k)
    have hM : HasDerivAt (fun t : ℝ => P.M₁ k (u0 + t • d - x k)) (P.M₁ k d) 0 :=
      (P.M₁ k).hasFDerivAt.comp_hasDerivAt (0:ℝ) hℓ'
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

theorem hy_rel {n m : ℕ} {v : Variant} {P : Data n m} {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun v P x z y) (k : ℕ) :
    y (k + 1) - y k = (P.ρ * P.r) • (P.A (x (k + 1)) - z (k + 1)) := by
  rw [(hrun k).2.2]; abel

theorem hQ_rel {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
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

theorem astar_rel {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    ContinuousLinearMap.adjoint P.A (y (k + 1))
      = -(gxOf v P (x k) (x (k + 1)) + P.M₁ k (x (k + 1) - x k))
        + (1 - 1 / P.ρ) • ContinuousLinearMap.adjoint P.A (y (k + 1) - y k) := by
  have h := hQ_rel v P hA x z y hrun k
  have h1 : ContinuousLinearMap.adjoint P.A (y (k + 1))
      = ContinuousLinearMap.adjoint P.A (y k) + ContinuousLinearMap.adjoint P.A (y (k + 1) - y k) := by
    rw [← map_add]; congr 1; abel
  have h2 : ContinuousLinearMap.adjoint P.A (y k)
      = -(gxOf v P (x k) (x (k + 1)) + P.M₁ k (x (k + 1) - x k))
        - (1 / P.ρ) • ContinuousLinearMap.adjoint P.A (y (k + 1) - y k) := by
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← h]; abel
  rw [h1, h2, sub_smul, one_smul]; abel

noncomputable def kapA {n m : ℕ} (v : Variant) (P : Data n m) : ℝ :=
  match v with
  | .prox => P.L + P.μ₁
  | .linearized => P.μ₁

noncomputable def kapB {n m : ℕ} (v : Variant) (P : Data n m) : ℝ :=
  match v with
  | .prox => P.μ₁
  | .linearized => P.L + P.μ₁

theorem C1_eq {n m : ℕ} (v : Variant) (P : Data n m) :
    C1 v P = 4 * T0 P * kapB v P ^ 2 / P.r := by cases v <;> rfl

theorem C3_eq {n m : ℕ} (v : Variant) (P : Data n m) :
    C3 v P = P.ρ * kapA v P / (Real.sqrt P.lam * (1 - |1 - P.ρ|)) := by cases v <;> rfl

theorem C4_eq {n m : ℕ} (v : Variant) (P : Data n m) :
    C4 v P = P.ρ * kapB v P / (Real.sqrt P.lam * (1 - |1 - P.ρ|)) := by cases v <;> rfl

theorem M1_norm_le {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (k : ℕ) (d : E n) :
    ‖P.M₁ k d‖ ≤ P.μ₁ * ‖d‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hA.μ₁_bound k) (norm_nonneg _))

theorem Qdec {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (k : ℕ) :
    ∃ E' : E n, gxOf v P (x k) (x (k + 1)) + P.M₁ k (x (k + 1) - x k)
        = gradient P.h (x (k + 1)) + E' ∧ ‖E'‖ ≤ kapB v P * ‖x (k + 1) - x k‖ := by
  cases v with
  | prox =>
    refine ⟨P.M₁ k (x (k + 1) - x k), by simp [gxOf], ?_⟩
    simpa [kapB] using M1_norm_le Variant.prox P hA k (x (k + 1) - x k)
  | linearized =>
    refine ⟨(gradient P.h (x k) - gradient P.h (x (k + 1))) + P.M₁ k (x (k + 1) - x k), by simp [gxOf]; abel, ?_⟩
    have h1 := hA.h_lip (x k) (x (k + 1))
    have h2 := M1_norm_le Variant.linearized P hA k (x (k + 1) - x k)
    have h3 : ‖x k - x (k + 1)‖ = ‖x (k + 1) - x k‖ := norm_sub_rev _ _
    calc _ ≤ ‖gradient P.h (x k) - gradient P.h (x (k + 1))‖ + ‖P.M₁ k (x (k + 1) - x k)‖ := norm_add_le _ _
      _ ≤ P.L * ‖x k - x (k + 1)‖ + P.μ₁ * ‖x (k + 1) - x k‖ := add_le_add h1 h2
      _ = kapB Variant.linearized P * ‖x (k + 1) - x k‖ := by rw [h3]; simp [kapB]; ring

theorem dQ_bound {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
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

theorem B_rec {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
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
  set B1 := ContinuousLinearMap.adjoint P.A (y (j + 1 + 1) - y (j + 1)) with hB1
  set B0 := ContinuousLinearMap.adjoint P.A (y (j + 1) - y j) with hB0
  set Q1 := gxOf v P (x (j + 1)) (x (j + 1 + 1)) + P.M₁ (j + 1) (x (j + 1 + 1) - x (j + 1)) with hQ1
  set Q0 := gxOf v P (x j) (x (j + 1)) + P.M₁ j (x (j + 1) - x j) with hQ0
  set a1 := ContinuousLinearMap.adjoint P.A (y (j + 1)) with ha1
  set a0 := ContinuousLinearMap.adjoint P.A (y j) with ha0
  have hB1' : B1 = -(P.ρ • Q1) - P.ρ • a1 := by
    have := congrArg (fun w => P.ρ • w) e1
    simp only [smul_add, smul_smul, smul_zero] at this
    rw [mul_one_div_cancel hρ, one_smul] at this
    rw [eq_sub_iff_add_eq, ← sub_eq_zero]
    rw [← this]; abel
  have hB0' : B0 = -(P.ρ • Q0) - P.ρ • a0 := by
    have := congrArg (fun w => P.ρ • w) e0
    simp only [smul_add, smul_smul, smul_zero] at this
    rw [mul_one_div_cancel hρ, one_smul] at this
    rw [eq_sub_iff_add_eq, ← sub_eq_zero]
    rw [← this]; abel
  have ha1' : a1 = a0 + B0 := by rw [← hd]; abel
  have this : P.ρ • a0 = -(P.ρ • Q0) - B0 := by rw [hB0']; abel
  have h5 : P.ρ • (a0 + B0) = P.ρ • a0 + P.ρ • B0 := smul_add _ _ _
  rw [hB1', ha1', h5, this, sub_smul, one_smul, smul_sub]
  abel

theorem res_norm {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    ‖P.A (x (k + 1)) - z (k + 1)‖ = 1 / (P.ρ * P.r) * ‖y (k + 1) - y k‖ := by
  have hpos : 0 < P.ρ * P.r := mul_pos hA.ρ_pos hA.r_pos
  rw [hy_rel hrun k, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, ← mul_assoc, one_div,
    inv_mul_cancel₀ hpos.ne', one_mul]

theorem l5_i {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (j : ℕ) :
    ‖z (j + 2) - z (j + 1)‖ ≤ ‖P.A‖ * ‖x (j + 2) - x (j + 1)‖ + ‖P.A (x (j + 2)) - z (j + 2)‖
          + ‖P.A (x (j + 1)) - z (j + 1)‖ ∧
      ‖P.A‖ * ‖x (j + 2) - x (j + 1)‖ + ‖P.A (x (j + 2)) - z (j + 2)‖ + ‖P.A (x (j + 1)) - z (j + 1)‖
        = ‖P.A‖ * ‖x (j + 2) - x (j + 1)‖ + 1 / (P.ρ * P.r) * ‖y (j + 2) - y (j + 1)‖
          + 1 / (P.ρ * P.r) * ‖y (j + 1) - y j‖ := by
  constructor
  · have e : z (j + 2) - z (j + 1) = P.A (x (j + 2) - x (j + 1)) - (P.A (x (j + 2)) - z (j + 2))
        + (P.A (x (j + 1)) - z (j + 1)) := by rw [map_sub]; abel
    rw [e]
    have h1 : ‖P.A (x (j + 2) - x (j + 1))‖ ≤ ‖P.A‖ * ‖x (j + 2) - x (j + 1)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    calc _ ≤ ‖P.A (x (j + 2) - x (j + 1)) - (P.A (x (j + 2)) - z (j + 2))‖
          + ‖P.A (x (j + 1)) - z (j + 1)‖ := norm_add_le _ _
      _ ≤ (‖P.A (x (j + 2) - x (j + 1))‖ + ‖P.A (x (j + 2)) - z (j + 2)‖)
          + ‖P.A (x (j + 1)) - z (j + 1)‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by gcongr
  · rw [res_norm v P hA x z y hrun (j + 1), res_norm v P hA x z y hrun j]

theorem l5_iii {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (j : ℕ) :
    ‖y (j + 2) - y (j + 1)‖ ≤ C3 v P * ‖x (j + 2) - x (j + 1)‖ + C4 v P * ‖x (j + 1) - x j‖
        + T2 P * (‖ContinuousLinearMap.adjoint P.A (y (j + 1) - y j)‖
          - ‖ContinuousLinearMap.adjoint P.A (y (j + 2) - y (j + 1))‖) := by
  have hρ0 := hA.ρ_pos
  have hρ2 := hA.ρ_lt
  have hlam := hA.lam_pos
  set s := Real.sqrt P.lam with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hlam
  set q := |1 - P.ρ| with hq
  have hq1 : q < 1 := by rw [hq, abs_lt]; constructor <;> linarith
  have hq0 : 0 ≤ q := abs_nonneg _
  have hsy : ∀ w : E m, s * ‖w‖ ≤ ‖ContinuousLinearMap.adjoint P.A w‖ := by
    intro w
    by_contra h
    push_neg at h
    have h2 := pow_lt_pow_left₀ h (norm_nonneg _) (two_ne_zero)
    have h3 := hA.lam_le w
    have h4 : (s * ‖w‖) ^ 2 = P.lam * ‖w‖ ^ 2 := by
      rw [mul_pow, hs, Real.sq_sqrt hlam.le]
    linarith
  set b1 := ‖ContinuousLinearMap.adjoint P.A (y (j + 2) - y (j + 1))‖ with hb1
  set b0 := ‖ContinuousLinearMap.adjoint P.A (y (j + 1) - y j)‖ with hb0
  set d1 := ‖x (j + 2) - x (j + 1)‖ with hd1
  set d0 := ‖x (j + 1) - x j‖ with hd0
  have hrec := B_rec v P hA x z y hrun j
  have hdQ := dQ_bound v P hA x j
  have hb : b1 ≤ q * b0 + P.ρ * (kapA v P * d1 + kapB v P * d0) := by
    rw [hb1]
    rw [hrec]
    calc _ ≤ ‖(1 - P.ρ) • ContinuousLinearMap.adjoint P.A (y (j + 1) - y j)‖
          + ‖P.ρ • ((gxOf v P (x (j + 1)) (x (j + 2)) + P.M₁ (j + 1) (x (j + 2) - x (j + 1)))
          - (gxOf v P (x j) (x (j + 1)) + P.M₁ j (x (j + 1) - x j)))‖ := norm_sub_le _ _
      _ ≤ q * b0 + P.ρ * (kapA v P * d1 + kapB v P * d0) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hρ0]
        gcongr
  have hy1 := hsy (y (j + 2) - y (j + 1))
  have hq1' : 0 < 1 - q := by linarith
  have hE : C3 v P * d1 + C4 v P * d0 + T2 P * (b0 - b1)
      = (P.ρ * (kapA v P * d1 + kapB v P * d0) + q * (b0 - b1)) / (s * (1 - q)) := by
    rw [C3_eq, C4_eq]
    unfold T2
    rw [← hs, ← hq]
    field_simp
  rw [hE, le_div_iff₀ (mul_pos hspos hq1')]
  have hkey : s * ‖y (j + 2) - y (j + 1)‖ ≤ b1 := hy1
  nlinarith [mul_le_mul_of_nonneg_right hkey hq1'.le]

theorem young2 (p q u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    (p + q) ^ 2 ≤ p ^ 2 / u + q ^ 2 / (1 - u) := by
  have h1u : 0 < 1 - u := by linarith
  rw [div_add_div _ _ hu0.ne' h1u.ne', le_div_iff₀ (mul_pos hu0 h1u)]
  nlinarith [sq_nonneg (p * (1 - u) - q * u)]

theorem core_ii (ρ lam r a e K b Y T0 T1 : ℝ) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) (hlam : 0 < lam)
    (hr : 0 < r) (ha : 0 ≤ a) (he : 0 ≤ e) (heK : e ≤ K) (hb : 0 ≤ b)
    (hT0 : T0 = if ρ ≤ 1 then 1 / (lam * ρ) else ρ / (lam * (2 - ρ) ^ 2))
    (hT1 : T1 = if ρ ≤ 1 then (1 - ρ) / (lam * ρ ^ 2 * r) else (ρ - 1) / (lam * (2 - ρ) * ρ * r))
    (hY : lam * Y ≤ (a + e + |1 - 1 / ρ| * b) ^ 2) :
    1 / (2 * r) * Y ≤ T1 / 2 * b ^ 2 + T0 / r * a ^ 2 + T0 / r * K ^ 2 := by
  have hp : (a + e) ^ 2 ≤ 2 * (a ^ 2 + K ^ 2) := by
    nlinarith [sq_nonneg (a - e), mul_self_le_mul_self he heK]
  have hY2 : 1 / (2 * r) * Y = (lam * Y) / (2 * r * lam) := by field_simp
  have hden : 0 < 2 * r * lam := by positivity
  rcases lt_trichotomy ρ 1 with h1 | h1 | h1
  · -- ρ < 1
    have hs0 : |1 - 1 / ρ| = (1 - ρ) / ρ := by
      rw [abs_of_nonpos]
      · field_simp; ring
      · have : 1 ≤ 1 / ρ := by rw [le_div_iff₀ hρ0]; linarith
        linarith
    have hy := hY.trans (young2 (a + e) (|1 - 1 / ρ| * b) ρ hρ0 h1)
    rw [hs0] at hy
    rw [hY2]
    have hle1 : lam * Y / (2 * r * lam) ≤ ((a + e) ^ 2 / ρ + ((1 - ρ) / ρ * b) ^ 2 / (1 - ρ)) / (2 * r * lam) :=
      div_le_div_of_nonneg_right hy hden.le
    refine hle1.trans ?_
    have hle2 : (a + e) ^ 2 / ρ ≤ 2 * (a ^ 2 + K ^ 2) / ρ := div_le_div_of_nonneg_right hp hρ0.le
    have h1ρ : (1 - ρ) ≠ 0 := by linarith
    have hle3 : ((a + e) ^ 2 / ρ + ((1 - ρ) / ρ * b) ^ 2 / (1 - ρ)) / (2 * r * lam)
        ≤ (2 * (a ^ 2 + K ^ 2) / ρ + ((1 - ρ) / ρ * b) ^ 2 / (1 - ρ)) / (2 * r * lam) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    refine hle3.trans (le_of_eq ?_)
    rw [hT0, hT1, if_pos h1.le, if_pos h1.le]
    field_simp
    ring
  · -- ρ = 1
    subst h1
    simp at hY
    have hy : lam * Y ≤ 2 * (a ^ 2 + K ^ 2) := hY.trans hp
    rw [hY2]
    have hle1 : lam * Y / (2 * r * lam) ≤ (2 * (a ^ 2 + K ^ 2)) / (2 * r * lam) :=
      div_le_div_of_nonneg_right hy hden.le
    refine hle1.trans (le_of_eq ?_)
    rw [hT0, hT1, if_pos le_rfl, if_pos le_rfl]
    field_simp
    ring
  · -- ρ > 1
    have h4 : (2 - ρ) ^ 2 < ρ := by nlinarith
    have hu0 : 0 < (2 - ρ) ^ 2 / ρ := by
      have : 0 < 2 - ρ := by linarith
      positivity
    have hu1 : (2 - ρ) ^ 2 / ρ < 1 := by rw [div_lt_one hρ0]; exact h4
    have hs0 : |1 - 1 / ρ| = (ρ - 1) / ρ := by
      rw [abs_of_nonneg]
      · field_simp
      · have : 1 / ρ ≤ 1 := by rw [div_le_iff₀ hρ0]; linarith
        linarith
    have hy := hY.trans (young2 (a + e) (|1 - 1 / ρ| * b) _ hu0 hu1)
    rw [hs0] at hy
    rw [hY2]
    have hle1 := div_le_div_of_nonneg_right hy hden.le
    refine hle1.trans ?_
    have h2ρ : 0 < 2 - ρ := by linarith
    have h4ρ : 0 < 4 - ρ := by linarith
    have hρ1 : 0 < ρ - 1 := by linarith
    have h1u : 1 - (2 - ρ) ^ 2 / ρ = (ρ - 1) * (4 - ρ) / ρ := by field_simp; ring
    rw [h1u]
    have hterm1 : (a + e) ^ 2 / ((2 - ρ) ^ 2 / ρ) ≤ 2 * (a ^ 2 + K ^ 2) / ((2 - ρ) ^ 2 / ρ) :=
      div_le_div_of_nonneg_right hp hu0.le
    have hterm2 : ((ρ - 1) / ρ * b) ^ 2 / ((ρ - 1) * (4 - ρ) / ρ)
        = (ρ - 1) / (ρ * (4 - ρ)) * b ^ 2 := by field_simp
    have hterm3 : (ρ - 1) / (ρ * (4 - ρ)) ≤ (ρ - 1) / ((2 - ρ) * ρ) := by
      apply div_le_div_of_nonneg_left hρ1.le (by positivity)
      nlinarith
    have hcomb : ((a + e) ^ 2 / ((2 - ρ) ^ 2 / ρ) + ((ρ - 1) / ρ * b) ^ 2 / ((ρ - 1) * (4 - ρ) / ρ)) / (2 * r * lam)
        ≤ (2 * (a ^ 2 + K ^ 2) / ((2 - ρ) ^ 2 / ρ) + (ρ - 1) / ((2 - ρ) * ρ) * b ^ 2) / (2 * r * lam) := by
      apply div_le_div_of_nonneg_right _ hden.le
      rw [hterm2]
      have := mul_le_mul_of_nonneg_right hterm3 (sq_nonneg b)
      linarith
    refine hcomb.trans (le_of_eq ?_)
    rw [hT0, hT1, if_neg (by linarith), if_neg (by linarith)]
    field_simp
    ring

theorem l5_ii {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    1 / (2 * P.r) * ‖y (k + 1)‖ ^ 2 ≤
      T1 P / 2 * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ ^ 2
        + T0 P / P.r * ‖gradient P.h (x (k + 1))‖ ^ 2 + C1 v P / 4 * ‖x (k + 1) - x k‖ ^ 2 := by
  obtain ⟨E', hE, hEn⟩ := Qdec v P hA x k
  have hast := astar_rel v P hA x z y hrun k
  rw [hE] at hast
  have hkB : 0 ≤ kapB v P := by
    have hT0pos : 0 < T0 P := by
      unfold T0
      have h1 := hA.lam_pos
      have h2 := hA.ρ_pos
      have h3 : 0 < 2 - P.ρ := by linarith [hA.ρ_lt]
      split_ifs with h
      · positivity
      · positivity
    have hLpos : 0 < P.L := by
      by_contra hh
      push Not at hh
      have : 4 * T0 P * P.L ≤ 0 := by nlinarith
      linarith [hA.eq14.2]
    cases v <;> simp only [kapB]
    · exact hA.μ₁_nonneg
    · linarith [hA.μ₁_nonneg]
  set a := ‖gradient P.h (x (k + 1))‖ with ha
  set e := ‖E'‖ with he
  set b := ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ with hb
  set d := ‖x (k + 1) - x k‖ with hd
  have hnorm : ‖ContinuousLinearMap.adjoint P.A (y (k + 1))‖ ≤ a + e + |1 - 1 / P.ρ| * b := by
    rw [hast]
    calc _ ≤ ‖-(gradient P.h (x (k + 1)) + E')‖
          + ‖(1 - 1 / P.ρ) • ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ := norm_add_le _ _
      _ ≤ (a + e) + |1 - 1 / P.ρ| * b := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs]
        gcongr
        exact norm_add_le _ _
  have hY : P.lam * ‖y (k + 1)‖ ^ 2 ≤ (a + e + |1 - 1 / P.ρ| * b) ^ 2 := by
    refine (hA.lam_le _).trans ?_
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcore := core_ii P.ρ P.lam P.r a e (kapB v P * d) b (‖y (k + 1)‖ ^ 2) (T0 P) (T1 P) hA.ρ_pos hA.ρ_lt
    hA.lam_pos hA.r_pos (norm_nonneg _) (norm_nonneg _) hEn (norm_nonneg _) rfl rfl hY
  have hC : C1 v P / 4 * d ^ 2 = T0 P / P.r * (kapB v P * d) ^ 2 := by
    rw [C1_eq]; field_simp
  rw [hC]; exact hcore


open NonconvexSplitting.Shared BotNguyenADMM.KL in
theorem solution {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) :
    (∀ k, 1 ≤ k →
      ‖z (k + 1) - z k‖ ≤ ‖P.A‖ * ‖x (k + 1) - x k‖ + ‖P.A (x (k + 1)) - z (k + 1)‖
          + ‖P.A (x k) - z k‖ ∧
      ‖P.A‖ * ‖x (k + 1) - x k‖ + ‖P.A (x (k + 1)) - z (k + 1)‖ + ‖P.A (x k) - z k‖
        = ‖P.A‖ * ‖x (k + 1) - x k‖ + 1 / (P.ρ * P.r) * ‖y (k + 1) - y k‖
          + 1 / (P.ρ * P.r) * ‖y k - y (k - 1)‖) ∧
    (∀ k, 1 / (2 * P.r) * ‖y (k + 1)‖ ^ 2 ≤
      T1 P / 2 * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ ^ 2
        + T0 P / P.r * ‖gradient P.h (x (k + 1))‖ ^ 2 + C1 v P / 4 * ‖x (k + 1) - x k‖ ^ 2) ∧
    (∀ k, 1 ≤ k →
      ‖y (k + 1) - y k‖ ≤ C3 v P * ‖x (k + 1) - x k‖ + C4 v P * ‖x k - x (k - 1)‖
        + T2 P * (‖ContinuousLinearMap.adjoint P.A (y k - y (k - 1))‖
          - ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖)) := by
  refine ⟨?_, fun k => l5_ii v P hA x z y hrun k, ?_⟩
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact l5_i v P hA x z y hrun j
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact l5_iii v P hA x z y hrun j
