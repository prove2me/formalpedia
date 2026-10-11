-- Prove2me | solution 1 for BotNguyenADMM.KL.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T12:47:51.739014+00:00
-- url     : https://prove2.me/submissions/f55e30d1-ab4c-4f19-a400-93968dca24f7

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_BotNguyenADMM_KL_Setting
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL BotNguyenADMM.KL
open Filter Topology
open scoped RealInnerProductSpace

set_option autoImplicit false


theorem bn_rec_summable (a b : ℕ → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (ha : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k) (hb : Summable b)
    (hrec : ∀ k, a (k + 1) ≤ θ * a k + b k) : Summable a := by
  set B := ∑' k, b k with hB
  have hbM : ∀ M, ∑ i ∈ Finset.range M, b i ≤ B := fun M => hb.sum_le_tsum _ (fun i _ => hb0 i)
  have hsucc : ∀ M, ∑ i ∈ Finset.range (M + 1), a i ≤ a 0 + θ * ∑ i ∈ Finset.range M, a i + B := by
    intro M
    rw [Finset.sum_range_succ']
    have h1 : ∑ i ∈ Finset.range M, a (i + 1) ≤ ∑ i ∈ Finset.range M, (θ * a i + b i) :=
      Finset.sum_le_sum (fun i _ => hrec i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    linarith [hbM M]
  have hmono : ∀ M, ∑ i ∈ Finset.range M, a i ≤ ∑ i ∈ Finset.range (M + 1), a i := by
    intro M; rw [Finset.sum_range_succ]; linarith [ha M]
  have hbound : ∀ M, ∑ i ∈ Finset.range M, a i ≤ (a 0 + B) / (1 - θ) := by
    intro M
    have h1 := hsucc M
    have h2 := hmono M
    have h3 : (1 - θ) * ∑ i ∈ Finset.range (M + 1), a i ≤ a 0 + B := by nlinarith
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  exact summable_of_sum_range_le ha hbound

theorem bn_amgm (κ K ε dd W δ : ℝ) (hκ : 0 < κ) (hK : 0 ≤ K) (hε : 0 < ε) (hd : 0 ≤ dd)
    (hW : 0 ≤ W) (hδ : 0 ≤ δ) (h : κ * dd ^ 2 ≤ δ * (K * W)) :
    dd ≤ ε * W + K / (4 * ε * κ) * δ := by
  set B := K / (4 * ε * κ) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hB : 4 * ε * κ * B = K := by rw [hBdef]; field_simp
  by_contra hcon
  push_neg at hcon
  have hT : 0 ≤ ε * W + B * δ := by positivity
  have h1 : (ε * W + B * δ) ^ 2 < dd ^ 2 := by nlinarith
  have h2 : 4 * (ε * W) * (B * δ) ≤ (ε * W + B * δ) ^ 2 := by nlinarith [sq_nonneg (ε * W - B * δ)]
  have h3 : κ * (4 * (ε * W) * (B * δ)) = δ * (K * W) := by rw [← hB]; ring
  have h4 : κ * (ε * W + B * δ) ^ 2 < κ * dd ^ 2 := by nlinarith
  nlinarith

theorem bn_tele (P : ℕ → ℝ) (N M : ℕ) :
    ∑ i ∈ Finset.range M, (P (N + i + 1) - P (N + i + 2)) = P (N + 1) - P (N + M + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have : N + (M + 1) + 1 = N + M + 2 := by omega
    rw [this]; ring

theorem bn_shift1 (f : ℕ → ℝ) (N M : ℕ) :
    ∑ i ∈ Finset.range M, f (N + i + 1) = ∑ i ∈ Finset.range (M + 1), f (N + i) - f N := by
  rw [Finset.sum_range_succ']
  simp only [add_zero]
  have : ∀ i, f (N + (i + 1)) = f (N + i + 1) := fun i => by rw [Nat.add_assoc]
  simp only [this]; ring

theorem bn_shift2 (f : ℕ → ℝ) (N M : ℕ) :
    ∑ i ∈ Finset.range M, f (N + i + 2) =
      ∑ i ∈ Finset.range (M + 2), f (N + i) - f N - f (N + 1) := by
  have h1 := bn_shift1 f (N + 1) M
  have h2 := bn_shift1 f N (M + 1)
  have e1 : ∀ i, f (N + 1 + i + 1) = f (N + i + 2) := fun i => by congr 1; omega
  have e2 : ∀ i, f (N + 1 + i) = f (N + i + 1) := fun i => by congr 1; omega
  simp only [e1, e2] at h1
  rw [h1, h2]

theorem bn_fl_core (d e P : ℕ → ℝ) (κ K θ c : ℝ) (N : ℕ) (hκ : 0 < κ) (hK : 0 ≤ K)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : 0 ≤ c)
    (hd : ∀ k, 0 ≤ d k) (he : ∀ k, 0 ≤ e k) (hP : ∀ k, N ≤ k → 0 ≤ P k)
    (hPdec : ∀ k, N ≤ k → P (k + 2) ≤ P (k + 1))
    (hkey : ∀ k, N ≤ k →
      κ * d (k + 2) ^ 2 ≤ (P (k + 1) - P (k + 2)) * (K * (d (k + 1) + e (k + 1) + e k)))
    (hrec : ∀ k, e (k + 1) ≤ θ * e k + c * (d (k + 1) + d k)) :
    Summable d := by
  set ε : ℝ := (1 - θ) / (2 * (1 - θ) + 8 * c) with hεdef
  have hε : 0 < ε := by rw [hεdef]; apply div_pos <;> nlinarith
  set B : ℝ := K / (4 * ε * κ) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have step : ∀ k, N ≤ k →
      d (k + 2) ≤ ε * (d (k + 1) + e (k + 1) + e k) + B * (P (k + 1) - P (k + 2)) := by
    intro k hk
    exact bn_amgm κ K ε _ _ _ hκ hK hε (hd _) (by linarith [hd (k+1), he (k+1), he k])
      (by linarith [hPdec k hk]) (hkey k hk)
  set s : ℕ → ℝ := fun M => ∑ i ∈ Finset.range M, d (N + i) with hs
  set t : ℕ → ℝ := fun M => ∑ i ∈ Finset.range M, e (N + i) with ht
  have hsm : ∀ M, s M ≤ s (M + 1) := by
    intro M; simp only [hs, Finset.sum_range_succ]; linarith [hd (N + M)]
  have htm : ∀ M, t M ≤ t (M + 1) := by
    intro M; simp only [ht, Finset.sum_range_succ]; linarith [he (N + M)]
  have hs0 : ∀ M, 0 ≤ s M := fun M => Finset.sum_nonneg (fun i _ => hd _)
  -- e sums
  have het : ∀ M, (1 - θ) * t M ≤ e N + 2 * c * s M := by
    intro M
    cases M with
    | zero => simp [ht, hs]; exact he N
    | succ M =>
      have h1 : ∑ i ∈ Finset.range M, e (N + i + 1) ≤
          ∑ i ∈ Finset.range M, (θ * e (N + i) + c * (d (N + i + 1) + d (N + i))) :=
        Finset.sum_le_sum (fun i _ => hrec (N + i))
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
        bn_shift1 e N M, bn_shift1 d N M] at h1
      have h2 : t (M + 1) - e N ≤ θ * t M + c * (s (M + 1) - d N + s M) := h1
      have h3 := htm M
      have h4 := hsm M
      have h5 := hd N
      nlinarith
  -- d sums
  have hds : ∀ M, s (M + 2) ≤ d N + d (N + 1) + ε * (s (M + 2) + 2 * t (M + 2)) + B * P (N + 1) := by
    intro M
    have h1 : ∑ i ∈ Finset.range M, d (N + i + 2) ≤
        ∑ i ∈ Finset.range M, (ε * (d (N + i + 1) + e (N + i + 1) + e (N + i))
          + B * (P (N + i + 1) - P (N + i + 2))) :=
      Finset.sum_le_sum (fun i _ => step (N + i) (by omega))
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, bn_tele P N M,
      Finset.sum_add_distrib, Finset.sum_add_distrib, bn_shift1 d N M, bn_shift1 e N M,
      bn_shift2 d N M] at h1
    have h2 : s (M + 2) - d N - d (N + 1) ≤
        ε * (s (M + 1) - d N + (t (M + 1) - e N) + t M) + B * (P (N + 1) - P (N + M + 1)) := h1
    have h3 := hsm (M + 1)
    have h4 := htm (M + 1)
    have h5 := htm M
    have h6 := hP (N + M + 1) (by omega)
    have h7 := hd N
    have h8 := he N
    have h9 : 0 ≤ t M := Finset.sum_nonneg (fun i _ => he _)
    nlinarith
  set C0 : ℝ := 2 * (d N + d (N + 1) + 2 * ε * e N / (1 - θ) + B * P (N + 1)) with hC0
  have hfin : ∀ M, s (M + 2) ≤ C0 := by
    intro M
    have h1 := hds M
    have h2 := het (M + 2)
    have h1θ : 0 < 1 - θ := by linarith
    have ht2 : t (M + 2) ≤ (e N + 2 * c * s (M + 2)) / (1 - θ) := by
      rw [le_div_iff₀ h1θ]; linarith
    have hεc : ε * (1 + 4 * c / (1 - θ)) = 1 / 2 := by
      rw [hεdef]; field_simp; ring
    have h3 : s (M + 2) ≤ d N + d (N + 1) + ε * s (M + 2)
        + 2 * ε * ((e N + 2 * c * s (M + 2)) / (1 - θ)) + B * P (N + 1) := by
      nlinarith
    have h4 : 2 * ε * ((e N + 2 * c * s (M + 2)) / (1 - θ))
        = 2 * ε * e N / (1 - θ) + ε * (4 * c / (1 - θ)) * s (M + 2) := by ring
    rw [h4] at h3
    have h5 : ε * s (M + 2) + ε * (4 * c / (1 - θ)) * s (M + 2) = s (M + 2) / 2 := by
      calc _ = ε * (1 + 4 * c / (1 - θ)) * s (M + 2) := by ring
        _ = s (M + 2) / 2 := by rw [hεc]; ring
    rw [hC0]
    linarith
  have hall : ∀ M, s M ≤ C0 := by
    intro M
    have : s M ≤ s (M + 2) := le_trans (hsm M) (hsm (M + 1))
    linarith [hfin M]
  have hsum : Summable (fun i => d (N + i)) := summable_of_sum_range_le (fun i => hd _) hall
  have : (fun i => d (i + N)) = fun i => d (N + i) := funext fun i => by rw [Nat.add_comm]
  rw [← summable_nat_add_iff N, this]
  exact hsum



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


theorem bn_descent_abstract {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
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
        - L * ‖d‖ ^ 2 / 2 * (((2:ℕ):ℝ) * t ^ (2 - 1))) t := this
    refine hgd.congr_deriv ?_
    norm_num
    ring
  have hanti : AntitoneOn g (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (fun t _ => (hg' t).continuousAt.continuousWithinAt)
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
    zero_pow two_ne_zero, mul_zero, sub_zero] at this
  have hpq : p + d = q := by rw [hd]; abel
  rw [hpq] at this
  nlinarith

theorem h_hasDeriv {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (p d : E n) :
    HasDerivAt (fun t : ℝ => P.h (p + t • d)) ⟪gradient P.h p, d⟫ 0 := by
  have := hpOf_deriv Variant.prox P hA.h_diff p p d
  simpa [hpOf, gxOf] using this

theorem h_up {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (p q : E n) :
    P.h q ≤ P.h p + ⟪gradient P.h p, q - p⟫ + P.L / 2 * ‖q - p‖ ^ 2 :=
  bn_descent_abstract P.h (gradient P.h) P.L (fun p d => h_hasDeriv v P hA p d) hA.h_lip p q

theorem h_low {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (p q : E n) :
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

theorem h_gx {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (x : ℕ → E n) (k : ℕ) :
    P.h (x (k + 1)) - P.h (x k) ≤
      ⟪gxOf v P (x k) (x (k + 1)), x (k + 1) - x k⟫ + P.L / 2 * ‖x (k + 1) - x k‖ ^ 2 := by
  cases v with
  | prox =>
    have h := h_low Variant.prox P hA (x (k + 1)) (x k)
    have e1 : x k - x (k + 1) = -(x (k + 1) - x k) := by abel
    rw [e1, inner_neg_right, norm_neg] at h
    simp only [gxOf]
    linarith
  | linearized =>
    have h := h_up Variant.linearized P hA (x k) (x (k + 1))
    simp only [gxOf]
    linarith

/-- real part of the augmented Lagrangian -/
noncomputable def R3 {n m : ℕ} (P : Data n m) (x : E n) (z y : E m) : ℝ :=
  P.h x + ⟪y, P.A x - z⟫ + P.r / 2 * ‖P.A x - z‖ ^ 2

theorem x_step {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
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

theorem y_step {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
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

theorem gz_fin {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
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

theorem gz_eq {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    P.g (z (k + 1)) = (((P.g (z (k + 1))).toReal : ℝ) : EReal) :=
  (EReal.coe_toReal (gz_fin v P hA x z y hrun k) (hA.g_proper.1 _)).symm

/-- the smooth part of the z-objective -/
noncomputable def Phi {n m : ℕ} (P : Data n m) (k : ℕ) (xk : E n) (zk yk : E m) (w : E m) : ℝ :=
  ⟪yk, P.A xk - w⟫ + P.r / 2 * ‖P.A xk - w‖ ^ 2 + 1 / 2 * ⟪P.M₂ k (w - zk), w - zk⟫

theorem z_step {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) (w : E m) (gw : ℝ)
    (hgw : P.g w = (gw : EReal)) :
    (P.g (z (k + 1))).toReal + Phi P k (x k) (z k) (y k) (z (k + 1))
      ≤ gw + Phi P k (x k) (z k) (y k) w := by
  have h := (hrun k).1 w
  unfold zObj at h
  rw [hgw, gz_eq v P hA x z y hrun k, ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h
  exact h

theorem CM_eq {n m : ℕ} (v : Variant) (P : Data n m) :
    CM v P = (4 * kapA v P ^ 2 + 6 * kapB v P ^ 2) * T0 P := by
  cases v <;> simp only [CM, kapA, kapB] <;> ring

theorem T0_pos {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) : 0 < T0 P := by
  have hl := hA.lam_pos; have h0 := hA.ρ_pos; have h2 := hA.ρ_lt
  unfold T0; split_ifs
  · positivity
  · have : 0 < 2 - P.ρ := by linarith
    positivity

theorem L_pos {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) : 0 < P.L := by
  have h1 := hA.eq14.2; have h2 := T0_pos v P hA
  by_contra hc; push_neg at hc
  nlinarith

theorem T1_nonneg {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) : 0 ≤ T1 P := by
  have hl := hA.lam_pos; have h0 := hA.ρ_pos; have h2 := hA.ρ_lt; have hr := hA.r_pos
  unfold T1; split_ifs with h
  · apply div_nonneg <;> nlinarith [mul_pos (mul_pos hl (mul_pos h0 h0)) hr]
  · push_neg at h
    apply div_nonneg
    · linarith
    · have : 0 < 2 - P.ρ := by linarith
      positivity

theorem T_ineq {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (E α ek : ℝ)
    (hE : 0 ≤ E) (hα : 0 ≤ α) (hek0 : 0 ≤ ek) (hek : ek ≤ |1 - P.ρ| * E + P.ρ * α) :
    ek ^ 2 / (P.lam * P.ρ * P.r) + T1 P * ek ^ 2 ≤ T1 P * E ^ 2 + T0 P / P.r * α ^ 2 := by
  have hl := hA.lam_pos; have h0 := hA.ρ_pos; have h2 := hA.ρ_lt; have hr := hA.r_pos
  unfold T0 T1
  split_ifs with h
  · rw [abs_of_nonneg (by linarith)] at hek
    have hsq : ek ^ 2 ≤ (1 - P.ρ) * E ^ 2 + P.ρ * α ^ 2 := by
      have h1 : ek ^ 2 ≤ ((1 - P.ρ) * E + P.ρ * α) ^ 2 := by
        apply pow_le_pow_left₀ hek0 hek
      nlinarith [mul_nonneg (mul_nonneg h0.le (by linarith : (0:ℝ) ≤ 1 - P.ρ)) (sq_nonneg (E - α))]
    have eL : ek ^ 2 / (P.lam * P.ρ * P.r) + (1 - P.ρ) / (P.lam * P.ρ ^ 2 * P.r) * ek ^ 2
        = ek ^ 2 / (P.lam * P.ρ ^ 2 * P.r) := by field_simp <;> ring
    have eR : (1 - P.ρ) / (P.lam * P.ρ ^ 2 * P.r) * E ^ 2 + 1 / (P.lam * P.ρ) / P.r * α ^ 2
        = ((1 - P.ρ) * E ^ 2 + P.ρ * α ^ 2) / (P.lam * P.ρ ^ 2 * P.r) := by field_simp <;> ring
    rw [eL, eR]
    exact div_le_div_of_nonneg_right hsq (by positivity)
  · push_neg at h
    rw [abs_of_neg (by linarith)] at hek
    have hb : 0 < 2 - P.ρ := by linarith
    have hek' : ek ≤ (P.ρ - 1) * E + P.ρ * α := by linarith
    have hsq : ek ^ 2 * (2 - P.ρ) ≤ (P.ρ - 1) * (2 - P.ρ) * E ^ 2 + P.ρ ^ 2 * α ^ 2 := by
      have h1 : ek ^ 2 ≤ ((P.ρ - 1) * E + P.ρ * α) ^ 2 := pow_le_pow_left₀ hek0 hek' 2
      have h3 : ((P.ρ - 1) * E + P.ρ * α) ^ 2 * (2 - P.ρ)
          ≤ (P.ρ - 1) * (2 - P.ρ) * E ^ 2 + P.ρ ^ 2 * α ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ P.ρ - 1) hb.le)
          (sq_nonneg ((2 - P.ρ) * E - P.ρ * α))]
      nlinarith
    have eL : ek ^ 2 / (P.lam * P.ρ * P.r) + (P.ρ - 1) / (P.lam * (2 - P.ρ) * P.ρ * P.r) * ek ^ 2
        = ek ^ 2 * (2 - P.ρ) / (P.lam * (2 - P.ρ) ^ 2 * P.ρ * P.r) := by
      field_simp <;> ring
    have eR : (P.ρ - 1) / (P.lam * (2 - P.ρ) * P.ρ * P.r) * E ^ 2
        + P.ρ / (P.lam * (2 - P.ρ) ^ 2) / P.r * α ^ 2
        = ((P.ρ - 1) * (2 - P.ρ) * E ^ 2 + P.ρ ^ 2 * α ^ 2) / (P.lam * (2 - P.ρ) ^ 2 * P.ρ * P.r) := by
      field_simp <;> ring
    rw [eL, eR]
    exact div_le_div_of_nonneg_right hsq (by positivity)

theorem M_inner_nonneg {N : ℕ} (T : E N →L[ℝ] E N) (hT : T.IsPositive) (u : E N) :
    0 ≤ ⟪T u, u⟫ := by
  have := hT.inner_nonneg_left u
  simpa using this

/-- the real value of F_r at W k = (x_{k+1}, z_{k+1}, y_{k+1}, x_k, y_k) -/
noncomputable def FR {n m : ℕ} (v : Variant) (P : Data n m) (x : ℕ → E n) (z y : ℕ → E m)
    (k : ℕ) : ℝ :=
  (P.g (z (k + 1))).toReal + R3 P (x (k + 1)) (z (k + 1)) (y (k + 1))
    + T1 P * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ ^ 2
    + C1 v P / 2 * ‖x (k + 1) - x k‖ ^ 2

theorem Fseq_eq {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    Fseq v P x z y (k + 1) = ((FR v P x z y k : ℝ) : EReal) := by
  unfold Fseq Fr
  simp only [Nat.add_sub_cancel]
  show Lr P (x (k + 1)) (z (k + 1)) (y (k + 1))
      + ((T1 P * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ ^ 2
        + C1 v P / 2 * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal) = _
  unfold Lr
  rw [gz_eq v P hA x z y hrun k, ← EReal.coe_add, ← EReal.coe_add]
  congr 1
  unfold FR R3
  ring

theorem descent_key (τ kA kB C1 CMr α d0 d1 : ℝ) (hτ : 0 < τ) (hkA : 0 ≤ kA) (hkB : 0 ≤ kB)
    (hα : 0 ≤ α) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hαle : α ≤ kA * d1 + kB * d0)
    (hC1 : C1 = 4 * kB ^ 2 * τ) (hCM : CMr = (4 * kA ^ 2 + 6 * kB ^ 2) * τ) :
    τ * α ^ 2 + (C1 / 2 + τ * (if kB = 0 then kA ^ 2 else kB ^ 2)) * d1 ^ 2
      ≤ 1 / 2 * CMr * d1 ^ 2 + C1 / 2 * d0 ^ 2 := by
  subst hC1 hCM
  split_ifs with h0
  · subst h0
    have hα1 : α ≤ kA * d1 := by linarith
    have h2 : α ^ 2 ≤ (kA * d1) ^ 2 := pow_le_pow_left₀ hα hα1 2
    nlinarith
  · have h2 : α ^ 2 ≤ (kA * d1 + kB * d0) ^ 2 := pow_le_pow_left₀ hα hαle 2
    nlinarith [sq_nonneg (kA * d1 - kB * d0)]

theorem descent {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ k, FR v P x z y (k + 1) + κ * ‖x (k + 2) - x (k + 1)‖ ^ 2
      ≤ FR v P x z y k := by
  have hT0 := T0_pos v P hA
  have hr := hA.r_pos
  have hL := L_pos v P hA
  have hμ := hA.μ₁_nonneg
  have hl := hA.lam_pos
  have hρ := hA.ρ_pos
  have hτ0 : 0 < T0 P / P.r := div_pos hT0 hr
  have hkA0 : 0 ≤ kapA v P := by cases v <;> simp [kapA] <;> linarith
  have hkB0 : 0 ≤ kapB v P := by cases v <;> simp [kapB] <;> linarith
  have hkAB : 0 < kapA v P + kapB v P := by cases v <;> simp [kapA, kapB] <;> linarith
  have hcpos : 0 < (if kapB v P = 0 then kapA v P ^ 2 else kapB v P ^ 2) := by
    split_ifs with h
    · have : 0 < kapA v P := by linarith
      positivity
    · exact pow_pos (lt_of_le_of_ne hkB0 (Ne.symm h)) 2
  refine ⟨T0 P / P.r * (if kapB v P = 0 then kapA v P ^ 2 else kapB v P ^ 2),
    mul_pos hτ0 hcpos, fun k => ?_⟩
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
  have h15 := hA.eq15 (k + 1) (x (k + 1 + 1) - x (k + 1))
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
  have hT := T_ineq v P hA _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hek
  have hdy : ‖y (k + 1 + 1) - y (k + 1)‖ ^ 2 / (P.ρ * P.r) ≤
      ‖ContinuousLinearMap.adjoint P.A (y (k + 2) - y (k + 1))‖ ^ 2 / (P.lam * P.ρ * P.r) := by
    have hρr : 0 < P.ρ * P.r := mul_pos hρ hr
    rw [div_le_div_iff₀ hρr (mul_pos (mul_pos hl hρ) hr)]
    have := hlam
    nlinarith
  have key := descent_key (T0 P / P.r) (kapA v P) (kapB v P) (C1 v P) (CM v P / P.r) _ _ _ hτ0
    hkA0 hkB0 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hdQ
    (by rw [C1_eq]; ring) (by rw [CM_eq]; ring)
  unfold FR
  have hR3k : R3 P (x (k + 1)) (z (k + 1)) (y (k + 1)) = P.h (x (k + 1))
      + (⟪y (k + 1), P.A (x (k + 1)) - z (k + 1)⟫ + P.r / 2 * ‖P.A (x (k + 1)) - z (k + 1)‖ ^ 2) := by
    unfold R3; ring
  rw [hR3k]
  have e2 : k + 1 + 1 = k + 2 := rfl
  simp only [e2] at hz hx hy h15 hM2 hdy ⊢
  linarith

theorem pack5_sub {n m : ℕ} (a a' : E n) (b b' c c' : E m) (d d' : E n) (e e' : E m) :
    pack5 a b c d e - pack5 a' b' c' d' e' = pack5 (a - a') (b - b') (c - c') (d - d') (e - e') := by
  simp only [pack5, ← WithLp.toLp_sub, Prod.mk_sub_mk]

theorem inner_pack5 {n m : ℕ} (a a' : E n) (b b' c c' : E m) (d d' : E n) (e e' : E m) :
    ⟪pack5 a b c d e, pack5 a' b' c' d' e'⟫ = ⟪a, a'⟫ + ⟪b, b'⟫ + ⟪c, c'⟫ + ⟪d, d'⟫ + ⟪e, e'⟫ := by
  simp [pack5, WithLp.prod_inner_apply]; ring

theorem normsq_pack5 {n m : ℕ} (a : E n) (b c : E m) (d : E n) (e : E m) :
    ‖pack5 a b c d e‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 + ‖e‖ ^ 2 := by
  simp [pack5, WithLp.prod_norm_sq_eq_of_L2]; ring

theorem pack5_eta {n m : ℕ} (u : Quint n m) : pack5 (qx u) (qz u) (qy u) (qx' u) (qy' u) = u := rfl

theorem norm_pack5_le {n m : ℕ} (a : E n) (b c : E m) (d : E n) (e : E m) :
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

theorem pack5_comp_le {n m : ℕ} (a : E n) (b c : E m) (d : E n) (e : E m) :
    ‖a‖ ≤ ‖pack5 a b c d e‖ ∧ ‖b‖ ≤ ‖pack5 a b c d e‖ ∧ ‖c‖ ≤ ‖pack5 a b c d e‖ ∧
      ‖d‖ ≤ ‖pack5 a b c d e‖ ∧ ‖e‖ ≤ ‖pack5 a b c d e‖ := by
  have h := normsq_pack5 a b c d e
  have f : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ ‖pack5 a b c d e‖ ^ 2 → t ≤ ‖pack5 a b c d e‖ :=
    fun t ht h2 => (pow_le_pow_iff_left₀ ht (norm_nonneg _) two_ne_zero).1 h2
  refine ⟨f _ (norm_nonneg _) ?_, f _ (norm_nonneg _) ?_, f _ (norm_nonneg _) ?_,
    f _ (norm_nonneg _) ?_, f _ (norm_nonneg _) ?_⟩ <;>
  nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖, sq_nonneg ‖c‖, sq_nonneg ‖d‖, sq_nonneg ‖e‖]

theorem reg_of_quad {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
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

theorem M_inner_le {N : ℕ} (T : E N →L[ℝ] E N) (μ : ℝ) (hT : ‖T‖ ≤ μ) (u : E N) :
    ⟪T u, u⟫ ≤ μ * ‖u‖ ^ 2 := by
  calc ⟪T u, u⟫ ≤ ‖T u‖ * ‖u‖ := real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖u‖) * ‖u‖ := by gcongr; exact T.le_opNorm u
    _ ≤ (μ * ‖u‖) * ‖u‖ := by gcongr
    _ = μ * ‖u‖ ^ 2 := by ring

/-- the subgradient of F_r at W k -/
noncomputable def Vsub {n m : ℕ} (v : Variant) (P : Data n m) (x : ℕ → E n) (z y : ℕ → E m)
    (k : ℕ) : Quint n m :=
  pack5
    (gradient P.h (x (k + 1))
      + ContinuousLinearMap.adjoint P.A (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1)))
      + C1 v P • (x (k + 1) - x k))
    ((y k + P.r • (P.A (x k) - z (k + 1)) - P.M₂ k (z (k + 1) - z k))
      - (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1))))
    ((P.A (x (k + 1)) - z (k + 1))
      + (2 * T1 P) • P.A (ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)))
    (-(C1 v P • (x (k + 1) - x k)))
    (-((2 * T1 P) • P.A (ContinuousLinearMap.adjoint P.A (y (k + 1) - y k))))

/-- W k = (x_{k+1}, z_{k+1}, y_{k+1}, x_k, y_k) -/
noncomputable def Wpt {n m : ℕ} (x : ℕ → E n) (z y : ℕ → E m) (k : ℕ) : Quint n m :=
  pack5 (x (k + 1)) (z (k + 1)) (y (k + 1)) (x k) (y k)

theorem Fr_W {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    Fr v P (Wpt x z y k) = ((FR v P x z y k : ℝ) : EReal) := by
  exact Fseq_eq v P hA x z y hrun k

theorem Fr_pack5 {n m : ℕ} (v : Variant) (P : Data n m) (X : E n) (Z Y : E m) (X' : E n) (Y' : E m) :
    Fr v P (pack5 X Z Y X' Y') = P.g Z + ((R3 P X Z Y
      + T1 P * ‖ContinuousLinearMap.adjoint P.A (Y - Y')‖ ^ 2 + C1 v P / 2 * ‖X - X'‖ ^ 2 : ℝ) : EReal) := by
  show Lr P X Z Y + _ = _
  unfold Lr R3
  rw [add_assoc, ← EReal.coe_add]
  congr 2
  simp only [qx, qx', qy, qy', pack5]
  ring

theorem C1_nonneg {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) : 0 ≤ C1 v P := by
  rw [C1_eq]; have := T0_pos v P hA; have := hA.r_pos; positivity

theorem palm_ereal_cases' (e : EReal) (he : e ≠ ⊥) : e = ⊤ ∨ ∃ r : ℝ, e = (r : EReal) := by
  by_cases h : e = ⊤
  · exact Or.inl h
  · exact Or.inr ⟨e.toReal, (EReal.coe_toReal h he).symm⟩

theorem quad_bound (L a r μ dx dz dy dx' dy' : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hμ : 0 ≤ μ) (hdx : 0 ≤ dx) (hdz : 0 ≤ dz) (hdy : 0 ≤ dy) :
    L / 2 * dx ^ 2 + dy * (a * dx + dz) + (r + μ) / 2 * dz ^ 2
      ≤ (L / 2 + a + 1 + (r + μ) / 2) * (dx ^ 2 + dz ^ 2 + dy ^ 2 + dx' ^ 2 + dy' ^ 2) := by
  nlinarith [sq_nonneg (dy - dx), sq_nonneg (dy - dz), mul_nonneg ha (sq_nonneg (dy - dx)),
    sq_nonneg dx', sq_nonneg dy', mul_nonneg hL (sq_nonneg dz), mul_nonneg hL (sq_nonneg dy),
    mul_nonneg ha (sq_nonneg dz), mul_nonneg (add_nonneg hr hμ) (sq_nonneg dx),
    mul_nonneg (add_nonneg hr hμ) (sq_nonneg dy), mul_nonneg hL (sq_nonneg dx'),
    mul_nonneg hL (sq_nonneg dy'), mul_nonneg ha (sq_nonneg dx'), mul_nonneg ha (sq_nonneg dy'),
    mul_nonneg (add_nonneg hr hμ) (sq_nonneg dx'), mul_nonneg (add_nonneg hr hμ) (sq_nonneg dy'),
    mul_nonneg ha (sq_nonneg dz), mul_nonneg ha (sq_nonneg dy)]

set_option maxHeartbeats 1000000 in
theorem V_minorant {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) (u' : Quint n m) :
    Fr v P (Wpt x z y k) + ((⟪Vsub v P x z y k, u' - Wpt x z y k⟫
      - (P.L / 2 + ‖P.A‖ + 1 + (P.r + P.μ₂) / 2) * ‖u' - Wpt x z y k‖ ^ 2 : ℝ) : EReal)
      ≤ Fr v P u' := by
  rw [← pack5_eta u']
  generalize qx u' = X
  generalize qz u' = Z
  generalize qy u' = Y
  generalize qx' u' = X'
  generalize qy' u' = Y'
  rw [Fr_W v P hA x z y hrun k, Fr_pack5]
  rcases palm_ereal_cases' (P.g Z) (hA.g_proper.1 Z) with h | ⟨gZ, hgZ⟩
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
  have I5 : ⟪Vsub v P x z y k, pack5 DX DZ DY DX' DY'⟫
      = ⟪gradient P.h (x (k + 1)), DX⟫ + ⟪y (k + 1), q⟫ + P.r * ⟪p, q⟫ + C1 v P * ⟪Δ, DX⟫
        + (⟪y k, DZ⟫ + P.r * ⟪p0, DZ⟫ - ⟪P.M₂ k a, DZ⟫) + ⟪p, DY⟫ + 2 * T1 P * ⟪P.A w, DY⟫
        - C1 v P * ⟪Δ, DX'⟫ - 2 * T1 P * ⟪P.A w, DY'⟫ := by
    unfold Vsub
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
    (norm_nonneg _) hA.r_pos.le hμ2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have B4a : 0 ≤ T1 P * ‖s‖ ^ 2 := mul_nonneg (T1_nonneg v P hA) (sq_nonneg _)
  have B4b : 0 ≤ C1 v P / 2 * ‖DX - DX'‖ ^ 2 :=
    mul_nonneg (div_nonneg (C1_nonneg v P hA) two_pos.le) (sq_nonneg _)
  have B4c : 0 ≤ P.r / 2 * ‖q‖ ^ 2 := mul_nonneg (div_nonneg hA.r_pos.le two_pos.le) (sq_nonneg _)
  rw [I6] at hz
  rw [I1, I3, I4, I5]
  unfold FR
  rw [I2]
  simp only [← hw, ← hΔ]
  have hc1 := real_inner_comm DY p
  linarith [hz, B1, B2, B3, B5, B4a, B4b, B4c, hc1]

theorem V_reg {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    IsRegularSubgrad (Fr v P) (Wpt x z y k) (Vsub v P x z y k) := by
  have hμ2 : 0 ≤ P.μ₂ := le_trans (norm_nonneg _) (hA.μ₂_bound 0)
  refine reg_of_quad _ _ _ (P.L / 2 + ‖P.A‖ + 1 + (P.r + P.μ₂) / 2)
    (by have := L_pos v P hA; have := hA.r_pos; positivity) ?_ (V_minorant v P hA x z y hrun k)
  rw [Fr_W v P hA x z y hrun k]; exact EReal.coe_ne_top _

theorem V_lim {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    Vsub v P x z y k ∈ LimitingSubdiff (Fr v P) (Wpt x z y k) := by
  refine ⟨(V_reg v P hA x z y hrun k).1, fun _ => Wpt x z y k, fun _ => Vsub v P x z y k,
    tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds, fun _ => V_reg v P hA x z y hrun k⟩

theorem e_rec {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    ‖ContinuousLinearMap.adjoint P.A (y (k + 2) - y (k + 1))‖ ≤
      |1 - P.ρ| * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖
      + P.ρ * (kapA v P + kapB v P) * (‖x (k + 2) - x (k + 1)‖ + ‖x (k + 1) - x k‖) := by
  have hB := B_rec v P hA x z y hrun k
  have hdQ := dQ_bound v P hA x k
  have hρ := hA.ρ_pos
  have hL := L_pos v P hA
  have hμ := hA.μ₁_nonneg
  have hkA0 : 0 ≤ kapA v P := by cases v <;> simp [kapA] <;> linarith
  have hkB0 : 0 ≤ kapB v P := by cases v <;> simp [kapB] <;> linarith
  have h1 : ‖ContinuousLinearMap.adjoint P.A (y (k + 2) - y (k + 1))‖ ≤
      |1 - P.ρ| * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖
      + P.ρ * ‖(gxOf v P (x (k + 1)) (x (k + 2)) + P.M₁ (k + 1) (x (k + 2) - x (k + 1)))
        - (gxOf v P (x k) (x (k + 1)) + P.M₁ k (x (k + 1) - x k))‖ := by
    rw [hB]
    refine le_trans (norm_sub_le _ _) (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hρ]
  have h2 : kapA v P * ‖x (k + 2) - x (k + 1)‖ + kapB v P * ‖x (k + 1) - x k‖ ≤
      (kapA v P + kapB v P) * (‖x (k + 2) - x (k + 1)‖ + ‖x (k + 1) - x k‖) := by
    nlinarith [norm_nonneg (x (k + 2) - x (k + 1)), norm_nonneg (x (k + 1) - x k)]
  have h3 := mul_le_mul_of_nonneg_left (le_trans hdQ h2) hρ.le
  linarith

theorem res_norm' {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    ‖P.A (x (k + 1)) - z (k + 1)‖ = ‖y (k + 1) - y k‖ / (P.ρ * P.r) := by
  have hpos : 0 < P.ρ * P.r := mul_pos hA.ρ_pos hA.r_pos
  rw [hy_rel hrun k, norm_smul, Real.norm_of_nonneg hpos.le, mul_div_cancel_left₀ _ hpos.ne']

theorem dy_le {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (u : E m) :
    ‖u‖ ≤ ‖ContinuousLinearMap.adjoint P.A u‖ / Real.sqrt P.lam := by
  have hl := hA.lam_pos
  have hs : 0 < Real.sqrt P.lam := Real.sqrt_pos.2 hl
  rw [le_div_iff₀ hs]
  have h1 : (‖u‖ * Real.sqrt P.lam) ^ 2 ≤ ‖ContinuousLinearMap.adjoint P.A u‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hl.le]; nlinarith [hA.lam_le u]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h1

theorem V_norm {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    ‖Vsub v P x z y k‖ ≤ (P.L + P.μ₁ + 2 * C1 v P + P.r * ‖P.A‖) * ‖x (k + 1) - x k‖
      + (1 + 4 * T1 P * ‖P.A‖) * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖
      + (1 + 1 / (P.ρ * P.r)) * ‖y (k + 1) - y k‖ + P.μ₂ * ‖z (k + 1) - z k‖ := by
  have hopt := xopt v P hA x z y hrun k
  have hC1 := C1_nonneg v P hA
  have hT1 := T1_nonneg v P hA
  have hr := hA.r_pos
  have hpos : 0 < P.ρ * P.r := mul_pos hA.ρ_pos hr
  set Δ := x (k + 1) - x k with hΔ
  set w := ContinuousLinearMap.adjoint P.A (y (k + 1) - y k) with hw
  have hVx : gradient P.h (x (k + 1))
      + ContinuousLinearMap.adjoint P.A (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1)))
      + C1 v P • Δ
      = (gradient P.h (x (k + 1)) - gxOf v P (x k) (x (k + 1))) + w - P.M₁ k Δ + C1 v P • Δ := by
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
      + C1 v P • Δ‖ ≤ P.L * ‖Δ‖ + ‖w‖ + P.μ₁ * ‖Δ‖ + C1 v P * ‖Δ‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, Real.norm_of_nonneg hC1]
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
    rw [norm_neg] at h2
    rw [norm_smul, Real.norm_of_nonneg hr.le] at h2
    have h3 := mul_le_mul_of_nonneg_left hAΔ hr.le
    linarith
  have hVyn : ‖(P.A (x (k + 1)) - z (k + 1)) + (2 * T1 P) • P.A w‖ ≤
      ‖y (k + 1) - y k‖ / (P.ρ * P.r) + 2 * T1 P * (‖P.A‖ * ‖w‖) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [res_norm' v P hA x z y hrun k, norm_smul, Real.norm_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_left hAw (by positivity : (0:ℝ) ≤ 2 * T1 P)
    linarith
  have hVan : ‖-(C1 v P • Δ)‖ = C1 v P * ‖Δ‖ := by rw [norm_neg, norm_smul, Real.norm_of_nonneg hC1]
  have hVbn : ‖-((2 * T1 P) • P.A w)‖ ≤ 2 * T1 P * (‖P.A‖ * ‖w‖) := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hAw (by positivity)
  have htot := norm_pack5_le
    (gradient P.h (x (k + 1))
      + ContinuousLinearMap.adjoint P.A (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1)))
      + C1 v P • Δ)
    ((y k + P.r • (P.A (x k) - z (k + 1)) - P.M₂ k (z (k + 1) - z k))
      - (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1))))
    ((P.A (x (k + 1)) - z (k + 1)) + (2 * T1 P) • P.A w)
    (-(C1 v P • Δ)) (-((2 * T1 P) • P.A w))
  have hV : Vsub v P x z y k = pack5
    (gradient P.h (x (k + 1))
      + ContinuousLinearMap.adjoint P.A (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1)))
      + C1 v P • Δ)
    ((y k + P.r • (P.A (x k) - z (k + 1)) - P.M₂ k (z (k + 1) - z k))
      - (y (k + 1) + P.r • (P.A (x (k + 1)) - z (k + 1))))
    ((P.A (x (k + 1)) - z (k + 1)) + (2 * T1 P) • P.A w)
    (-(C1 v P • Δ)) (-((2 * T1 P) • P.A w)) := rfl
  rw [hV]
  rw [hVx] at htot ⊢
  rw [hVz] at htot ⊢
  have hdiv : ‖y (k + 1) - y k‖ / (P.ρ * P.r) = 1 / (P.ρ * P.r) * ‖y (k + 1) - y k‖ := by ring
  rw [hdiv] at hVyn
  nlinarith [hVxn, hVzn, hVyn, hVan, hVbn, norm_nonneg w, norm_nonneg Δ, norm_nonneg P.A]

theorem sq_diff_le {N : ℕ} (u v : E N) : ‖u‖ ^ 2 - ‖v‖ ^ 2 ≤ ‖u - v‖ * (‖u‖ + ‖v‖) := by
  have h1 : ‖u‖ - ‖v‖ ≤ ‖u - v‖ := norm_sub_norm_le u v
  have h2 : 0 ≤ ‖u‖ + ‖v‖ := by positivity
  nlinarith

theorem Phi_diff {n m : ℕ} (P : Data n m) (hμ : ∀ k, ‖P.M₂ k‖ ≤ P.μ₂) (hr : 0 ≤ P.r) (k : ℕ)
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
  nlinarith [mul_le_mul_of_nonneg_left t2 (by positivity : (0:ℝ) ≤ P.r / 2)]

theorem g_lim {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (R : ℝ)
    (hR : ∀ k, ‖x k‖ ≤ R ∧ ‖z k‖ ≤ R ∧ ‖y k‖ ≤ R)
    (φ : ℕ → ℕ) (zs : E m) (hφ : Tendsto (fun j => z (φ j + 1)) atTop (𝓝 zs)) :
    ∃ gs : ℝ, P.g zs = (gs : EReal) ∧
      Tendsto (fun j => (P.g (z (φ j + 1))).toReal) atTop (𝓝 gs) := by
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
    have := mul_le_mul_of_nonneg_left (add_le_add n1 n2) (by positivity : (0:ℝ) ≤ P.r / 2)
    have := mul_le_mul_of_nonneg_left (add_le_add n3 n4) (by positivity : (0:ℝ) ≤ P.μ₂ / 2)
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
    push_neg at hcon
    have hev := hφ.eventually (hA.g_lsc zs (U : EReal) hcon)
    obtain ⟨j, hj⟩ := hev.exists
    rw [gz_eq v P hA x z y hrun (φ j)] at hj
    have := hup (φ j)
    have : (U : ℝ) < (P.g (z (φ j + 1))).toReal := by exact_mod_cast hj
    linarith
  have hne : P.g zs ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top U) hle
  refine ⟨(P.g zs).toReal, (EReal.coe_toReal hne (hA.g_proper.1 zs)).symm, ?_⟩
  set gs := (P.g zs).toReal with hgs
  have hgs' : P.g zs = (gs : EReal) := (EReal.coe_toReal hne (hA.g_proper.1 zs)).symm
  rw [tendsto_order]
  constructor
  · intro c hc
    have hc' : (c : EReal) < P.g zs := by rw [hgs']; exact_mod_cast hc
    filter_upwards [hφ.eventually (hA.g_lsc zs (c : EReal) hc')] with j hj
    rw [gz_eq v P hA x z y hrun (φ j)] at hj
    exact_mod_cast hj
  · intro c hc
    have hdist : Tendsto (fun j => C ‖zs‖ * ‖zs - z (φ j + 1)‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j => ‖z (φ j + 1) - zs‖) atTop (𝓝 0) :=
        (tendsto_iff_norm_sub_tendsto_zero.1 hφ)
      have h2 := h1.const_mul (C ‖zs‖)
      rw [mul_zero] at h2
      refine h2.congr (fun j => ?_)
      rw [norm_sub_rev]
    filter_upwards [hdist.eventually (gt_mem_nhds (show (0:ℝ) < c - gs by linarith))] with j hj
    have h1 := z_step v P hA x z y hrun (φ j) zs gs hgs'
    have h2 := hPd (φ j) zs
    linarith

theorem Phi_expand {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (k : ℕ)
    (xk : E n) (zk yk z1 D : E m) :
    Phi P k xk zk yk (z1 + D) = Phi P k xk zk yk z1
      - ⟪yk + P.r • (P.A xk - z1) - P.M₂ k (z1 - zk), D⟫ + P.r / 2 * ‖D‖ ^ 2
      + 1 / 2 * ⟪P.M₂ k D, D⟫ := by
  have hsymm : ∀ u u' : E m, ⟪P.M₂ k u, u'⟫ = ⟪u, P.M₂ k u'⟫ :=
    fun u u' => (hA.M₂_pos k).isSymmetric u u'
  have e1 : P.A xk - (z1 + D) = (P.A xk - z1) - D := by abel
  have e2 : z1 + D - zk = (z1 - zk) + D := by abel
  have e3 : ⟪P.M₂ k ((z1 - zk) + D), (z1 - zk) + D⟫ = ⟪P.M₂ k (z1 - zk), z1 - zk⟫
      + 2 * ⟪P.M₂ k (z1 - zk), D⟫ + ⟪P.M₂ k D, D⟫ := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsymm D (z1 - zk),
      real_inner_comm (P.M₂ k (z1 - zk)) D]
    ring
  unfold Phi
  rw [e1, e2, e3, inner_sub_right, norm_sub_sq_real]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
  ring

theorem xi_reg {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (k : ℕ) :
    IsRegularSubgrad P.g (z (k + 1))
      (y k + P.r • (P.A (x k) - z (k + 1)) - P.M₂ k (z (k + 1) - z k)) := by
  have hμ0 : 0 ≤ P.μ₂ := le_trans (norm_nonneg _) (hA.μ₂_bound 0)
  refine reg_of_quad _ _ _ ((P.r + P.μ₂) / 2) (by have := hA.r_pos; positivity)
    (gz_fin v P hA x z y hrun k) (fun Z => ?_)
  rcases palm_ereal_cases' (P.g Z) (hA.g_proper.1 Z) with h | ⟨gZ, hgZ⟩
  · rw [h]; exact le_top
  rw [hgZ, gz_eq v P hA x z y hrun k, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hz := z_step v P hA x z y hrun k Z gZ hgZ
  obtain ⟨D, rfl⟩ : ∃ D, Z = z (k + 1) + D := ⟨Z - z (k + 1), by abel⟩
  rw [Phi_expand v P hA] at hz
  simp only [add_sub_cancel_left]
  have := M_inner_le (P.M₂ k) P.μ₂ (hA.μ₂_bound k) D
  nlinarith

theorem FR_lb {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) (R : ℝ)
    (hR : ∀ k, ‖x k‖ ≤ R ∧ ‖z k‖ ≤ R ∧ ‖y k‖ ≤ R) :
    ∃ c0 : ℝ, ∀ k, c0 ≤ FR v P x z y k := by
  obtain ⟨cg, hcg⟩ := hA.g_bdd
  obtain ⟨ch, hch⟩ := hA.h_bdd
  refine ⟨cg + ch - R * (‖P.A‖ * R + R), fun k => ?_⟩
  have h1 : cg ≤ (P.g (z (k + 1))).toReal := by
    have := hcg (z (k + 1)); rw [gz_eq v P hA x z y hrun k] at this; exact_mod_cast this
  have h2 := hch (x (k + 1))
  obtain ⟨hx, hz, hy⟩ := hR (k + 1)
  have hAx : ‖P.A (x (k + 1))‖ ≤ ‖P.A‖ * R :=
    (P.A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hp : ‖P.A (x (k + 1)) - z (k + 1)‖ ≤ ‖P.A‖ * R + R := (norm_sub_le _ _).trans (by linarith)
  have h3 : -(R * (‖P.A‖ * R + R)) ≤ ⟪y (k + 1), P.A (x (k + 1)) - z (k + 1)⟫ := by
    have := neg_le_of_abs_le (abs_real_inner_le_norm (y (k + 1)) (P.A (x (k + 1)) - z (k + 1)))
    have h4 : ‖y (k + 1)‖ * ‖P.A (x (k + 1)) - z (k + 1)‖ ≤ R * (‖P.A‖ * R + R) :=
      mul_le_mul hy hp (norm_nonneg _) (le_trans (norm_nonneg _) hy)
    linarith
  have h5 : 0 ≤ P.r / 2 * ‖P.A (x (k + 1)) - z (k + 1)‖ ^ 2 := by
    have := hA.r_pos; positivity
  have h6 : 0 ≤ T1 P * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ ^ 2 :=
    mul_nonneg (T1_nonneg v P hA) (sq_nonneg _)
  have h7 : 0 ≤ C1 v P / 2 * ‖x (k + 1) - x k‖ ^ 2 :=
    mul_nonneg (div_nonneg (C1_nonneg v P hA) two_pos.le) (sq_nonneg _)
  unfold FR R3
  linarith
theorem palm_uniformized_KL {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [ProperSpace X] (F : X → EReal) (K : Set X) (c : ℝ) (hK : IsCompact K) (hKne : K.Nonempty)
    (hconst : ∀ a ∈ K, F a = (c : EReal))
    (hcrit : ∀ a ∈ K, (0 : X) ∈ LimitingSubdiff F a)
    (hKL : ∀ a, (LimitingSubdiff F a).Nonempty → HasKLProperty F a) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ η : ℝ, 0 < η ∧ ∃ φ : ℝ → ℝ, IsDesingularizer η φ ∧
      ∀ z : X, Metric.infDist z K < ε → ∀ s : ℝ, F z = (s : EReal) → c < s → s < c + η →
        ∀ v ∈ LimitingSubdiff F z, 1 ≤ deriv φ (s - c) * ‖v‖ := by
  classical
  have hex : ∀ a ∈ K, ∃ η : ℝ, 0 < η ∧ ∃ V ∈ 𝓝 a, ∃ φ : ℝ → ℝ,
      IsDesingularizer η φ ∧ KLIneq F a η V φ :=
    fun a ha => hKL a ⟨0, hcrit a ha⟩
  choose! ηf hηpos Vf hVf φf hdes hkl using hex
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun a => interior (Vf a))
    (fun a ha => interior_mem_nhds.2 (hVf a ha))
  have htne : t.Nonempty := by
    obtain ⟨a0, ha0⟩ := hKne
    have := hcover ha0
    simp only [Set.mem_iUnion] at this
    obtain ⟨a, hat, _⟩ := this
    exact ⟨a, hat⟩
  have hW : IsOpen (⋃ a ∈ t, interior (Vf a)) := isOpen_biUnion (fun a _ => isOpen_interior)
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hW hcover
  have hmin : ∀ s : Finset X, (∀ a ∈ s, 0 < ηf a) → ∃ η : ℝ, 0 < η ∧ ∀ a ∈ s, η ≤ ηf a := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _; exact ⟨1, one_pos, by simp⟩
    · intro b s hb ih hall
      obtain ⟨η, hη, hle⟩ := ih (fun a ha => hall a (Finset.mem_insert_of_mem ha))
      refine ⟨min η (ηf b), lt_min hη (hall b (Finset.mem_insert_self _ _)), ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle a ha)
  obtain ⟨η, hη, hηle⟩ := hmin t (fun a ha => hηpos a (htK a ha))
  have hconc : ∀ s : Finset X, (∀ a ∈ s, ConcaveOn ℝ (Set.Ico 0 η) (φf a)) →
      ConcaveOn ℝ (Set.Ico 0 η) (fun r => ∑ a ∈ s, φf a r) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using (concaveOn_const (0 : ℝ) (convex_Ico (0 : ℝ) η))
    · intro b s hb ih hall
      have h1 := hall b (Finset.mem_insert_self _ _)
      have h2 := ih (fun a ha => hall a (Finset.mem_insert_of_mem ha))
      have heq : (fun r => ∑ a ∈ insert b s, φf a r) = φf b + fun r => ∑ a ∈ s, φf a r := by
        funext r
        simp [Finset.sum_insert hb]
      rw [heq]
      exact h1.add h2
  have hdiff : ∀ a ∈ t, ∀ r ∈ Set.Ioo (0:ℝ) η, DifferentiableAt ℝ (φf a) r := by
    intro a ha r hr
    have hr' : r ∈ Set.Ioo (0:ℝ) (ηf a) := ⟨hr.1, lt_of_lt_of_le hr.2 (hηle a ha)⟩
    exact ((hdes a (htK a ha)).2.2.2.2.1.differentiableOn one_ne_zero).differentiableAt
      (Ioo_mem_nhds hr'.1 hr'.2)
  have hderiv : ∀ r ∈ Set.Ioo (0:ℝ) η, deriv (fun r => ∑ a ∈ t, φf a r) r =
      ∑ a ∈ t, deriv (φf a) r := fun r hr => deriv_fun_sum (fun a ha => hdiff a ha r hr)
  have hdesφ : IsDesingularizer η (fun r => ∑ a ∈ t, φf a r) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact continuousOn_finsetSum t (fun a ha =>
        ((hdes a (htK a ha)).1).mono (Set.Ico_subset_Ico_right (hηle a ha)))
    · exact hconc t (fun a ha => ((hdes a (htK a ha)).2.1).subset
        (Set.Ico_subset_Ico_right (hηle a ha)) (convex_Ico _ _))
    · intro r hr
      exact Finset.sum_nonneg (fun a ha => (hdes a (htK a ha)).2.2.1 r
        ⟨hr.1, lt_of_lt_of_le hr.2 (hηle a ha)⟩)
    · exact Finset.sum_eq_zero (fun a ha => (hdes a (htK a ha)).2.2.2.1)
    · exact ContDiffOn.sum (fun a ha => ((hdes a (htK a ha)).2.2.2.2.1).mono
        (Set.Ioo_subset_Ioo_right (hηle a ha)))
    · intro r hr
      rw [hderiv r hr]
      refine Finset.sum_pos (fun a ha => ?_) htne
      exact (hdes a (htK a ha)).2.2.2.2.2 r ⟨hr.1, lt_of_lt_of_le hr.2 (hηle a ha)⟩
  refine ⟨δ, hδ, η, hη, fun r => ∑ a ∈ t, φf a r, hdesφ, ?_⟩
  intro z hz s hFz hcs hsc v hv
  have hzth : z ∈ Metric.thickening δ K := (Metric.mem_thickening_iff_infDist_lt hKne).2 hz
  have hzW := hthick hzth
  simp only [Set.mem_iUnion] at hzW
  obtain ⟨a, hat, hzV⟩ := hzW
  have hrs : s - c ∈ Set.Ioo (0:ℝ) η := ⟨by linarith, by linarith⟩
  have hk := hkl a (htK a hat) z (interior_subset hzV)
    (by rw [hconst a (htK a hat), hFz]; exact_mod_cast hcs)
    (by
      rw [hconst a (htK a hat), hFz]
      have : ((s : ℝ) : EReal) < ((c + ηf a : ℝ) : EReal) := by
        exact_mod_cast (by have := hηle a hat; linarith : s < c + ηf a)
      simpa [EReal.coe_add] using this) v hv
  have hsub : (F z - F a).toReal = s - c := by
    rw [hconst a (htK a hat), hFz, ← EReal.coe_sub, EReal.toReal_coe]
  rw [hsub] at hk
  rw [hderiv _ hrs]
  have hle : deriv (φf a) (s - c) ≤ ∑ b ∈ t, deriv (φf b) (s - c) :=
    Finset.single_le_sum (f := fun b => deriv (φf b) (s - c))
      (fun b hb => (hdes b (htK b hb)).2.2.2.2.2 _ ⟨hrs.1, lt_of_lt_of_le hrs.2 (hηle b hb)⟩ |>.le)
      hat
  exact hk.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg v))


theorem pack3_comp_le {n m : ℕ} (a : E n) (b c : E m) :
    ‖a‖ ≤ ‖pack3 a b c‖ ∧ ‖b‖ ≤ ‖pack3 a b c‖ ∧ ‖c‖ ≤ ‖pack3 a b c‖ := by
  have h : ‖pack3 a b c‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 := by
    simp [pack3, WithLp.prod_norm_sq_eq_of_L2]; ring
  have f : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ ‖pack3 a b c‖ ^ 2 → t ≤ ‖pack3 a b c‖ :=
    fun t ht h2 => (pow_le_pow_iff_left₀ ht (norm_nonneg _) two_ne_zero).1 h2
  refine ⟨f _ (norm_nonneg _) ?_, f _ (norm_nonneg _) ?_, f _ (norm_nonneg _) ?_⟩ <;>
  nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖, sq_nonneg ‖c‖]

theorem pack5_tendsto {n m : ℕ} (a : ℕ → E n) (b c : ℕ → E m) (d : ℕ → E n) (e : ℕ → E m)
    (A : E n) (B C : E m) (D : E n) (E' : E m)
    (h : Tendsto (fun j => pack5 (a j) (b j) (c j) (d j) (e j)) atTop (𝓝 (pack5 A B C D E'))) :
    Tendsto a atTop (𝓝 A) ∧ Tendsto b atTop (𝓝 B) ∧ Tendsto c atTop (𝓝 C) ∧
      Tendsto d atTop (𝓝 D) ∧ Tendsto e atTop (𝓝 E') := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  simp only [pack5_sub] at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [tendsto_iff_norm_sub_tendsto_zero] <;>
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) h
  · exact (pack5_comp_le _ _ _ _ _).1
  · exact (pack5_comp_le _ _ _ _ _).2.1
  · exact (pack5_comp_le _ _ _ _ _).2.2.1
  · exact (pack5_comp_le _ _ _ _ _).2.2.2.1
  · exact (pack5_comp_le _ _ _ _ _).2.2.2.2

theorem kl_step (φ : ℝ → ℝ) (η a b κ dd Vn : ℝ) (hφ : IsDesingularizer η φ) (hb0 : 0 ≤ b)
    (hba : b ≤ a) (haη : a < η) (hκ : 0 ≤ κ) (hdec : κ * dd ^ 2 ≤ a - b)
    (hKL : 0 < a → 1 ≤ deriv φ a * Vn) (hVn : 0 ≤ Vn) :
    0 ≤ φ a - φ b ∧ κ * dd ^ 2 ≤ (φ a - φ b) * Vn := by
  rcases hba.lt_or_eq with hlt | heq
  · have ha0 : 0 < a := lt_of_le_of_lt hb0 hlt
    have hmem : a ∈ Set.Ioo 0 η := ⟨ha0, haη⟩
    have hdiff : DifferentiableAt ℝ φ a :=
      (hφ.2.2.2.2.1.differentiableOn one_ne_zero).differentiableAt (Ioo_mem_nhds ha0 haη)
    have hsl : deriv φ a ≤ slope φ b a :=
      hφ.2.1.deriv_le_slope (Set.mem_Ico.2 ⟨hb0, by linarith⟩) (Set.mem_Ico.2 ⟨ha0.le, haη⟩)
        hlt hdiff
    rw [slope_def_field] at hsl
    have hab : 0 < a - b := sub_pos.2 hlt
    have hΔ : deriv φ a * (a - b) ≤ φ a - φ b := by
      rw [le_div_iff₀ hab] at hsl; exact hsl
    have hφ'pos : 0 < deriv φ a := hφ.2.2.2.2.2 _ hmem
    have hΔ0 : 0 ≤ φ a - φ b := le_trans (mul_nonneg hφ'pos.le hab.le) hΔ
    refine ⟨hΔ0, ?_⟩
    have hK := hKL ha0
    have h2 : a - b ≤ (a - b) * (deriv φ a * Vn) := le_mul_of_one_le_right hab.le hK
    have h3 : (a - b) * (deriv φ a * Vn) ≤ (φ a - φ b) * Vn := by
      have := mul_le_mul_of_nonneg_right hΔ hVn
      nlinarith
    linarith
  · rw [heq] at hdec ⊢
    simp only [sub_self, zero_mul, le_refl, true_and]
    linarith

theorem conv_sq (θ c a b s : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hs : 0 ≤ s) (h : a ≤ θ * b + c * s) :
    a ^ 2 ≤ θ * b ^ 2 + (2 * c ^ 2 / (1 - θ)) * (s ^ 2 / 2) := by
  have h1θ : 0 < 1 - θ := by linarith
  have h1 : a ^ 2 ≤ (θ * b + c * s) ^ 2 := pow_le_pow_left₀ ha h 2
  have h2 : (θ * b + c * s) ^ 2 ≤ θ * b ^ 2 + c ^ 2 * s ^ 2 / (1 - θ) := by
    set w := c * s / (1 - θ) with hwdef
    have hw : c * s = (1 - θ) * w := by rw [hwdef]; field_simp
    have h3 : (θ * b + (1 - θ) * w) ^ 2 ≤ θ * b ^ 2 + (1 - θ) * w ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hθ0 h1θ.le) (sq_nonneg (b - w))]
    have h4 : (1 - θ) * w ^ 2 = c ^ 2 * s ^ 2 / (1 - θ) := by
      rw [hwdef]; field_simp
    rw [hw]; linarith
  have e2 : (2 * c ^ 2 / (1 - θ)) * (s ^ 2 / 2) = c ^ 2 * s ^ 2 / (1 - θ) := by
    field_simp
  linarith

theorem sq_summable_tendsto (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) (hs : Summable (fun k => f k ^ 2)) :
    Tendsto f atTop (𝓝 0) := by
  have h1 := hs.tendsto_atTop_zero
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
  rw [Real.sqrt_zero] at h2
  refine h2.congr (fun k => ?_)
  simp [Real.sqrt_sq (hf k)]

theorem dz_le {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
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

theorem V_bound2 {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j, ‖Vsub v P x z y (j + 1)‖ ≤ K * (‖x (j + 2) - x (j + 1)‖
      + ‖ContinuousLinearMap.adjoint P.A (y (j + 2) - y (j + 1))‖
      + ‖ContinuousLinearMap.adjoint P.A (y (j + 1) - y j)‖) := by
  have hC1 := C1_nonneg v P hA
  have hT1 := T1_nonneg v P hA
  have hr := hA.r_pos
  have hL := L_pos v P hA
  have hμ1 := hA.μ₁_nonneg
  have hμ2 : 0 ≤ P.μ₂ := le_trans (norm_nonneg _) (hA.μ₂_bound 0)
  have hpos : 0 < P.ρ * P.r := mul_pos hA.ρ_pos hr
  have hs : 0 < Real.sqrt P.lam := Real.sqrt_pos.2 hA.lam_pos
  set a1 := P.L + P.μ₁ + 2 * C1 v P + P.r * ‖P.A‖ with ha1
  set a2 := 1 + 4 * T1 P * ‖P.A‖ with ha2
  set b := 1 + 1 / (P.ρ * P.r) with hb
  set σ := 1 / Real.sqrt P.lam with hσ
  set β := 1 / (P.ρ * P.r) with hβ
  have ha1n : 0 ≤ a1 := by positivity
  have ha2n : 0 ≤ a2 := by positivity
  have hbn : 0 ≤ b := by positivity
  have hσn : 0 ≤ σ := by positivity
  have hβn : 0 ≤ β := by positivity
  refine ⟨(a1 + P.μ₂ * ‖P.A‖) + (a2 + b * σ + P.μ₂ * β * σ) + P.μ₂ * β * σ, by positivity,
    fun j => ?_⟩
  have hV := V_norm v P hA x z y hrun (j + 1)
  have hdz := dz_le v P hA x z y hrun j
  have hy1 := dy_le v P hA (y (j + 2) - y (j + 1))
  have hy0 := dy_le v P hA (y (j + 1) - y j)
  simp only [show j + 1 + 1 = j + 2 from rfl] at hV
  set d1 := ‖x (j + 2) - x (j + 1)‖
  set e1 := ‖ContinuousLinearMap.adjoint P.A (y (j + 2) - y (j + 1))‖
  set e0 := ‖ContinuousLinearMap.adjoint P.A (y (j + 1) - y j)‖
  have hd1 : 0 ≤ d1 := norm_nonneg _
  have he1 : 0 ≤ e1 := norm_nonneg _
  have he0 : 0 ≤ e0 := norm_nonneg _
  have hy1' : ‖y (j + 2) - y (j + 1)‖ ≤ σ * e1 := by rw [hσ]; rw [div_eq_mul_one_div] at hy1; linarith
  have hy0' : ‖y (j + 1) - y j‖ ≤ σ * e0 := by rw [hσ]; rw [div_eq_mul_one_div] at hy0; linarith
  have hdz' : ‖z (j + 2) - z (j + 1)‖ ≤ ‖P.A‖ * d1 + β * (σ * e1 + σ * e0) := by
    rw [hβ]
    have : (‖y (j + 2) - y (j + 1)‖ + ‖y (j + 1) - y j‖) / (P.ρ * P.r)
        ≤ 1 / (P.ρ * P.r) * (σ * e1 + σ * e0) := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have t1 := mul_le_mul_of_nonneg_left hy1' hbn
  have t2 := mul_le_mul_of_nonneg_left hdz' hμ2
  have hfin : ‖Vsub v P x z y (j + 1)‖ ≤ (a1 + P.μ₂ * ‖P.A‖) * d1
      + (a2 + b * σ + P.μ₂ * β * σ) * e1 + (P.μ₂ * β * σ) * e0 := by
    nlinarith
  have hc1 : 0 ≤ (a2 + b * σ + P.μ₂ * β * σ) + P.μ₂ * β * σ := by positivity
  have hc2 : 0 ≤ (a1 + P.μ₂ * ‖P.A‖) + P.μ₂ * β * σ := by positivity
  have hc3 : 0 ≤ (a1 + P.μ₂ * ‖P.A‖) + (a2 + b * σ + P.μ₂ * β * σ) := by positivity
  nlinarith [mul_nonneg hc1 hd1, mul_nonneg hc2 he1, mul_nonneg hc3 he0]

theorem grad_tend {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (u : ℕ → E n)
    (a : E n) (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun k => gradient P.h (u k)) atTop (𝓝 (gradient P.h a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hu ⊢
  have h := hu.const_mul P.L
  rw [mul_zero] at h
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => hA.h_lip _ _) h

theorem gx_tend {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P) (x : ℕ → E n)
    (a : E n) (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto (fun k => gxOf v P (x k) (x (k + 1))) atTop (𝓝 (gradient P.h a)) := by
  cases v with
  | prox => exact grad_tend Variant.prox P hA _ a (hx.comp (tendsto_add_atTop_nat 1))
  | linearized => exact grad_tend Variant.linearized P hA _ a hx

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL BotNguyenADMM.KL Filter Topology in
theorem solution {n m : ℕ} (v : Variant) (P : Data n m) (hA : Assumption1 v P)
    (x : ℕ → E n) (z y : ℕ → E m) (hrun : IsRun v P x z y)
    (hbdd : Bornology.IsBounded (Set.range fun k => pack3 (x k) (z k) (y k)))
    (hKL : IsKLFunction (Fr v P)) :
    (Summable (fun k => ‖x (k + 1) - x k‖) ∧ Summable (fun k => ‖z (k + 1) - z k‖) ∧
      Summable (fun k => ‖y (k + 1) - y k‖)) ∧
    ∃ (xh : E n) (zh yh : E m), IsKKTPoint P xh zh yh ∧
      Tendsto x atTop (𝓝 xh) ∧ Tendsto z atTop (𝓝 zh) ∧ Tendsto y atTop (𝓝 yh) := by
  classical
  obtain ⟨R, hR0⟩ := hbdd.exists_norm_le
  have hR : ∀ k, ‖x k‖ ≤ R ∧ ‖z k‖ ≤ R ∧ ‖y k‖ ≤ R := fun k => by
    have h := hR0 _ ⟨k, rfl⟩
    obtain ⟨h1, h2, h3⟩ := pack3_comp_le (x k) (z k) (y k)
    exact ⟨h1.trans h, h2.trans h, h3.trans h⟩
  have hρ := hA.ρ_pos
  have hr := hA.r_pos
  have hpos : 0 < P.ρ * P.r := mul_pos hρ hr
  obtain ⟨κ, hκ, hdec⟩ := descent v P hA x z y hrun
  obtain ⟨c0, hc0⟩ := FR_lb v P hA x z y hrun R hR
  have hanti : Antitone (FR v P x z y) := antitone_nat_of_succ_le (fun k => by
    have := hdec k; nlinarith [sq_nonneg ‖x (k + 2) - x (k + 1)‖])
  have hFc : Tendsto (FR v P x z y) atTop (𝓝 (⨅ k, FR v P x z y k)) :=
    tendsto_atTop_ciInf hanti ⟨c0, by rintro _ ⟨k, rfl⟩; exact hc0 k⟩
  set Fs := ⨅ k, FR v P x z y k with hFs
  have hFge : ∀ k, Fs ≤ FR v P x z y k := fun k => hanti.le_of_tendsto hFc k
  -- d and e
  have hd0 : ∀ k, 0 ≤ ‖x (k + 1) - x k‖ := fun k => norm_nonneg _
  have he0 : ∀ k, 0 ≤ ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ := fun k => norm_nonneg _
  have hd2 : Summable (fun k => ‖x (k + 1) - x k‖ ^ 2) := by
    have hpart : ∀ M, ∑ i ∈ Finset.range M, ‖x (i + 2) - x (i + 1)‖ ^ 2
        ≤ (FR v P x z y 0 - c0) / κ := by
      intro M
      have htel : ∑ i ∈ Finset.range M, (FR v P x z y i - FR v P x z y (i + 1))
          = FR v P x z y 0 - FR v P x z y M := Finset.sum_range_sub' _ M
      have hle : ∑ i ∈ Finset.range M, κ * ‖x (i + 2) - x (i + 1)‖ ^ 2
          ≤ ∑ i ∈ Finset.range M, (FR v P x z y i - FR v P x z y (i + 1)) :=
        Finset.sum_le_sum (fun i _ => by have := hdec i; linarith)
      rw [← Finset.mul_sum, htel] at hle
      rw [le_div_iff₀ hκ]; linarith [hc0 M]
    have := summable_of_sum_range_le (fun i => sq_nonneg _) hpart
    exact (summable_nat_add_iff 1).1 this
  -- the e recursion
  set θ := |1 - P.ρ| with hθ
  have hθ0 : 0 ≤ θ := abs_nonneg _
  have hθ1 : θ < 1 := by rw [hθ, abs_lt]; constructor <;> linarith [hA.ρ_lt]
  have hkA0 : 0 ≤ kapA v P := by
    have := L_pos v P hA; have := hA.μ₁_nonneg; cases v <;> simp [kapA] <;> linarith
  have hkB0 : 0 ≤ kapB v P := by
    have := L_pos v P hA; have := hA.μ₁_nonneg; cases v <;> simp [kapB] <;> linarith
  set c := P.ρ * (kapA v P + kapB v P) with hc
  have hc0' : 0 ≤ c := by positivity
  have hrec : ∀ k, ‖ContinuousLinearMap.adjoint P.A (y (k + 1 + 1) - y (k + 1))‖ ≤
      θ * ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖
      + c * (‖x (k + 1 + 1) - x (k + 1)‖ + ‖x (k + 1) - x k‖) := fun k => by
    have := e_rec v P hA x z y hrun k
    rw [hθ, hc]; exact this
  have he2 : Summable (fun k => ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ ^ 2) := by
    refine bn_rec_summable (fun k => ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖ ^ 2)
      (fun k => (2 * c ^ 2 / (1 - θ)) * (‖x (k + 1 + 1) - x (k + 1)‖ ^ 2 + ‖x (k + 1) - x k‖ ^ 2))
      θ hθ0 hθ1 (fun k => sq_nonneg _) (fun k => by
        have : 0 < 1 - θ := by linarith
        positivity) ?_ (fun k => ?_)
    · exact (((summable_nat_add_iff 1).2 hd2).add hd2).mul_left _
    · have h := conv_sq θ c _ _ _ hθ0 hθ1 hc0' (norm_nonneg _) (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) (hrec k)
      have hs : (‖x (k + 1 + 1) - x (k + 1)‖ + ‖x (k + 1) - x k‖) ^ 2 / 2
          ≤ ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2 + ‖x (k + 1) - x k‖ ^ 2 := by
        nlinarith [sq_nonneg (‖x (k + 1 + 1) - x (k + 1)‖ - ‖x (k + 1) - x k‖)]
      have hcc : 0 ≤ 2 * c ^ 2 / (1 - θ) := by
        have : 0 < 1 - θ := by linarith
        positivity
      have := mul_le_mul_of_nonneg_left hs hcc
      beta_reduce
      linarith
  have hdt : Tendsto (fun k => ‖x (k + 1) - x k‖) atTop (𝓝 0) :=
    sq_summable_tendsto _ hd0 hd2
  have het : Tendsto (fun k => ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖) atTop (𝓝 0) :=
    sq_summable_tendsto _ he0 he2
  -- the subgradients tend to zero
  obtain ⟨K', hK'0, hVb⟩ := V_bound2 v P hA x z y hrun
  have hV0 : Tendsto (fun k => Vsub v P x z y k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => K' * (‖x (j + 2) - x (j + 1)‖
        + ‖ContinuousLinearMap.adjoint P.A (y (j + 2) - y (j + 1))‖
        + ‖ContinuousLinearMap.adjoint P.A (y (j + 1) - y j)‖)) atTop (𝓝 0) := by
      have := (((hdt.comp (tendsto_add_atTop_nat 1)).add (het.comp (tendsto_add_atTop_nat 1))).add
        het).const_mul K'
      rw [show K' * (0 + 0 + 0) = (0:ℝ) by ring] at this
      exact this
    have h2 : Tendsto (fun j => Vsub v P x z y (j + 1)) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun j => norm_nonneg _) hVb h1)
    exact (tendsto_add_atTop_iff_nat 1).1 h2
  -- cluster set
  set W : ℕ → Quint n m := Wpt x z y with hW
  set Ω : Set (Quint n m) := {w | MapClusterPt w atTop W} with hΩ
  have hWb : Bornology.IsBounded (Set.range W) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨5 * R, ?_⟩
    rintro _ ⟨k, rfl⟩
    have h := norm_pack5_le (x (k + 1)) (z (k + 1)) (y (k + 1)) (x k) (y k)
    have := hR k; have := hR (k + 1)
    show ‖pack5 (x (k + 1)) (z (k + 1)) (y (k + 1)) (x k) (y k)‖ ≤ 5 * R
    linarith
  have hΩclosed : IsClosed Ω := isClosed_setOfPred_clusterPt
  have hΩsub : Ω ⊆ closure (Set.range W) := by
    intro w hw
    rw [mem_closure_iff_clusterPt]
    exact ClusterPt.mono hw (le_principal_iff.2 (range_mem_map))
  have hΩcomp : IsCompact Ω := hWb.isCompact_closure.of_isClosed_subset hΩclosed hΩsub
  have hΩne : Ω.Nonempty := by
    obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hWb (fun k => Set.mem_range_self k)
    exact ⟨a, MapClusterPt.of_comp hφ.tendsto_atTop hlim.mapClusterPt⟩
  have hdist : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Metric.infDist (W k) Ω < ε := by
    intro ε hε
    by_contra hcon
    have hfreq : ∃ᶠ k in atTop, ¬ Metric.infDist (W k) Ω < ε := by
      simpa [Filter.Eventually, Filter.Frequently] using hcon
    obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
    obtain ⟨a, -, ψ2, hψ2, hlim⟩ := tendsto_subseq_of_bounded hWb
      (x := fun j => W (φ j)) (fun j => Set.mem_range_self _)
    have haΩ : a ∈ Ω :=
      MapClusterPt.of_comp (hφ.tendsto_atTop.comp hψ2.tendsto_atTop) hlim.mapClusterPt
    have hcont : Tendsto (fun j => Metric.infDist (W (φ (ψ2 j))) Ω) atTop
        (𝓝 (Metric.infDist a Ω)) :=
      ((Metric.continuous_infDist_pt Ω).tendsto a).comp hlim
    have h0 : Metric.infDist a Ω = 0 := (hΩclosed.mem_iff_infDist_zero hΩne).1 haΩ
    rw [h0] at hcont
    obtain ⟨j, hj⟩ := (hcont.eventually (gt_mem_nhds hε)).exists
    exact hφP (ψ2 j) hj
  have hcl : ∀ u ∈ Ω, Fr v P u = (Fs : EReal) ∧ (0 : Quint n m) ∈ LimitingSubdiff (Fr v P) u := by
    intro u hu
    obtain ⟨φ, hφ, hlim⟩ := hu.tendsto_subseq
    have hu5 : u = pack5 (qx u) (qz u) (qy u) (qx' u) (qy' u) := (pack5_eta u).symm
    have hcomp := pack5_tendsto (fun j => x (φ j + 1)) (fun j => z (φ j + 1)) (fun j => y (φ j + 1))
      (fun j => x (φ j)) (fun j => y (φ j)) (qx u) (qz u) (qy u) (qx' u) (qy' u)
      (by rw [← hu5]; exact hlim)
    obtain ⟨hx1, hz1, hy1, hx0, hy0⟩ := hcomp
    obtain ⟨gs, hgs, hgt⟩ := g_lim v P hA x z y hrun R hR φ (qz u) hz1
    have hFφ : Tendsto (fun j => FR v P x z y (φ j)) atTop (𝓝 Fs) := hFc.comp hφ.tendsto_atTop
    have hAx : Tendsto (fun j => P.A (x (φ j + 1)) - z (φ j + 1)) atTop
        (𝓝 (P.A (qx u) - qz u)) := ((P.A.continuous.tendsto _).comp hx1).sub hz1
    have hR3 : Tendsto (fun j => R3 P (x (φ j + 1)) (z (φ j + 1)) (y (φ j + 1))) atTop
        (𝓝 (R3 P (qx u) (qz u) (qy u))) :=
      (((hA.h_diff.continuous.tendsto _).comp hx1).add (hy1.inner hAx)).add
        ((hAx.norm.pow 2).const_mul _)
    have hT : Tendsto (fun j => T1 P * ‖ContinuousLinearMap.adjoint P.A (y (φ j + 1) - y (φ j))‖ ^ 2)
        atTop (𝓝 (T1 P * ‖ContinuousLinearMap.adjoint P.A (qy u - qy' u)‖ ^ 2)) :=
      (((((ContinuousLinearMap.adjoint P.A).continuous.tendsto _).comp (hy1.sub hy0)).norm).pow
        2).const_mul _
    have hC : Tendsto (fun j => C1 v P / 2 * ‖x (φ j + 1) - x (φ j)‖ ^ 2) atTop
        (𝓝 (C1 v P / 2 * ‖qx u - qx' u‖ ^ 2)) := (((hx1.sub hx0).norm).pow 2).const_mul _
    have hFφ' : Tendsto (fun j => FR v P x z y (φ j)) atTop
        (𝓝 (gs + R3 P (qx u) (qz u) (qy u) + T1 P * ‖ContinuousLinearMap.adjoint P.A (qy u - qy' u)‖ ^ 2
          + C1 v P / 2 * ‖qx u - qx' u‖ ^ 2)) := ((hgt.add hR3).add hT).add hC
    have hval := tendsto_nhds_unique hFφ hFφ'
    have hFru : Fr v P u = (Fs : EReal) := by
      rw [hu5, Fr_pack5, hgs, ← EReal.coe_add, hval]
      congr 1; ring
    refine ⟨hFru, by rw [hFru]; exact EReal.coe_ne_top _, fun j => W (φ j),
      fun j => Vsub v P x z y (φ j), hlim, ?_, hV0.comp hφ.tendsto_atTop,
      fun j => V_reg v P hA x z y hrun (φ j)⟩
    have : (fun j => Fr v P (W (φ j))) = fun j => ((FR v P x z y (φ j) : ℝ) : EReal) :=
      funext fun j => Fr_W v P hA x z y hrun (φ j)
    rw [this, hFru]
    exact EReal.tendsto_coe.2 hFφ
  obtain ⟨ε, hε, η, hη, ψ, hψ, hKLu⟩ := palm_uniformized_KL (Fr v P) Ω Fs hΩcomp hΩne
    (fun a ha => (hcl a ha).1) (fun a ha => (hcl a ha).2) hKL.2.2
  have hev1 : ∀ᶠ k in atTop, FR v P x z y k - Fs < η := by
    have := hFc.eventually (gt_mem_nhds (show Fs < Fs + η by linarith))
    filter_upwards [this] with k hk using by linarith
  obtain ⟨N, hN⟩ := (hev1.and (hdist ε hε)).exists_forall_of_atTop
  have hstep : ∀ k, N ≤ k →
      0 ≤ ψ (FR v P x z y (k + 1) - Fs) - ψ (FR v P x z y (k + 2) - Fs) ∧
      κ * ‖x (k + 3) - x (k + 2)‖ ^ 2 ≤
        (ψ (FR v P x z y (k + 1) - Fs) - ψ (FR v P x z y (k + 2) - Fs)) * ‖Vsub v P x z y (k + 1)‖ := by
    intro k hk
    have hd' := hdec (k + 1)
    simp only [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl] at hd'
    refine kl_step ψ η _ _ κ _ _ hψ (by linarith [hFge (k + 2)])
      (by linarith [hanti (show k + 1 ≤ k + 2 by omega)]) (hN (k + 1) (by omega)).1 hκ.le
      (by linarith) (fun hpos' => ?_) (norm_nonneg _)
    have hfin := Fr_W v P hA x z y hrun (k + 1)
    exact hKLu (W (k + 1)) (hN (k + 1) (by omega)).2 (FR v P x z y (k + 1)) hfin
      (by linarith) (by linarith [(hN (k + 1) (by omega)).1]) _ (V_lim v P hA x z y hrun (k + 1))
  have hdsum : Summable (fun k => ‖x (k + 1) - x k‖) := by
    refine bn_fl_core (fun k => ‖x (k + 1) - x k‖)
      (fun k => ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖)
      (fun k => ψ (FR v P x z y k - Fs)) κ K' θ c N hκ hK'0 hθ0 hθ1 hc0' hd0 he0
      (fun k hk => hψ.2.2.1 _ ⟨by linarith [hFge k], (hN k hk).1⟩)
      (fun k hk => by have := (hstep k hk).1; beta_reduce; linarith)
      (fun k hk => ?_) hrec
    have h1 := (hstep k hk).2
    have h3 := mul_le_mul_of_nonneg_left (hVb k) (hstep k hk).1
    exact le_trans h1 h3
  have hesum : Summable (fun k => ‖ContinuousLinearMap.adjoint P.A (y (k + 1) - y k)‖) :=
    bn_rec_summable _ (fun k => c * (‖x (k + 1 + 1) - x (k + 1)‖ + ‖x (k + 1) - x k‖)) θ hθ0 hθ1
      he0 (fun k => by positivity) ((((summable_nat_add_iff 1).2 hdsum).add hdsum).mul_left c) hrec
  have hysum : Summable (fun k => ‖y (k + 1) - y k‖) :=
    (hesum.div_const (Real.sqrt P.lam)).of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => dy_le v P hA _)
  have hzsum : Summable (fun k => ‖z (k + 1) - z k‖) := by
    have h : Summable (fun k => ‖z (k + 2) - z (k + 1)‖) := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => dz_le v P hA x z y hrun k) ?_
      exact (((summable_nat_add_iff 1).2 hdsum).mul_left ‖P.A‖).add
        ((((summable_nat_add_iff 1).2 hysum).add hysum).div_const _)
    exact (summable_nat_add_iff 1).1 h
  -- limits
  have hcx : CauchySeq x := by
    refine cauchySeq_of_summable_dist (hdsum.congr (fun k => ?_))
    rw [dist_comm, dist_eq_norm]
  have hcz : CauchySeq z := by
    refine cauchySeq_of_summable_dist (hzsum.congr (fun k => ?_))
    rw [dist_comm, dist_eq_norm]
  have hcy : CauchySeq y := by
    refine cauchySeq_of_summable_dist (hysum.congr (fun k => ?_))
    rw [dist_comm, dist_eq_norm]
  obtain ⟨xh, hxh⟩ := cauchySeq_tendsto_of_complete hcx
  obtain ⟨zh, hzh⟩ := cauchySeq_tendsto_of_complete hcz
  obtain ⟨yh, hyh⟩ := cauchySeq_tendsto_of_complete hcy
  have hx1 : Tendsto (fun k => x (k + 1)) atTop (𝓝 xh) := hxh.comp (tendsto_add_atTop_nat 1)
  have hz1 : Tendsto (fun k => z (k + 1)) atTop (𝓝 zh) := hzh.comp (tendsto_add_atTop_nat 1)
  -- z = A x
  have hres : Tendsto (fun k => P.A (x (k + 1)) - z (k + 1)) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    have := hysum.tendsto_atTop_zero.div_const (P.ρ * P.r)
    rw [zero_div] at this
    exact this.congr (fun k => (res_norm' v P hA x z y hrun k).symm)
  have hres' : Tendsto (fun k => P.A (x (k + 1)) - z (k + 1)) atTop (𝓝 (P.A xh - zh)) :=
    ((P.A.continuous.tendsto _).comp hx1).sub hz1
  have hzA : zh = P.A xh := (sub_eq_zero.1 (tendsto_nhds_unique hres' hres)).symm
  -- gradient condition
  have hM1 : Tendsto (fun k => P.M₁ k (x (k + 1) - x k)) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
      (fun k => M1_norm_le v P hA k _) ?_)
    have := hdsum.tendsto_atTop_zero.const_mul P.μ₁
    rwa [mul_zero] at this
  have hsum0 := ((gx_tend v P hA x xh hxh).add
    (((ContinuousLinearMap.adjoint P.A).continuous.tendsto _).comp
      (hyh.add (hres'.const_smul P.r)))).add hM1
  have hzero : gradient P.h xh + ContinuousLinearMap.adjoint P.A (yh + P.r • (P.A xh - zh)) + 0 = 0 :=
    tendsto_nhds_unique hsum0 (tendsto_const_nhds.congr (fun k => (xopt v P hA x z y hrun k).symm))
  rw [hzA, sub_self, smul_zero, add_zero, add_zero] at hzero
  have hK1 : -(ContinuousLinearMap.adjoint P.A yh) = gradient P.h xh := by
    rw [neg_eq_iff_add_eq_zero, add_comm]; exact hzero
  -- subgradient condition
  obtain ⟨gs, hgs, hgt⟩ := g_lim v P hA x z y hrun R hR id zh hz1
  have hK2 : yh ∈ LimitingSubdiff P.g zh := by
    refine ⟨by rw [hgs]; exact EReal.coe_ne_top _, fun k => z (k + 1),
      fun k => y k + P.r • (P.A (x k) - z (k + 1)) - P.M₂ k (z (k + 1) - z k), hz1, ?_, ?_,
      fun k => xi_reg v P hA x z y hrun k⟩
    · have : (fun k => P.g (z (k + 1))) = fun k => (((P.g (z (k + 1))).toReal : ℝ) : EReal) :=
        funext fun k => gz_eq v P hA x z y hrun k
      rw [this, hgs]
      exact EReal.tendsto_coe.2 hgt
    · have hM2 : Tendsto (fun k => P.M₂ k (z (k + 1) - z k)) atTop (𝓝 0) := by
        refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
          (fun k => (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hA.μ₂_bound k) (norm_nonneg _))) ?_)
        have := hzsum.tendsto_atTop_zero.const_mul P.μ₂
        rwa [mul_zero] at this
      have h1 : Tendsto (fun k => P.A (x k) - z (k + 1)) atTop (𝓝 (P.A xh - zh)) :=
        ((P.A.continuous.tendsto _).comp hxh).sub hz1
      have h2 := (hyh.add (h1.const_smul P.r)).sub hM2
      rw [hzA, sub_self, smul_zero, add_zero, sub_zero] at h2
      exact h2
  exact ⟨⟨hdsum, hzsum, hysum⟩, xh, zh, yh, ⟨hK1, hK2, hzA⟩, hxh, hzh, hyh⟩
