-- Prove2me | solution 1 for BotNguyenADMM.Rates.theorem_20_prox_mu1_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:45:27.857198+00:00
-- url     : https://prove2.me/submissions/a3576bfa-162e-4cb7-9277-d6e696c7e978

import Mathlib
import Definitions.Def_BotNguyenADMM_Rates_Setting
import Definitions.Def_BotNguyenADMM_Rates_Lojasiewicz
import Theorems.Thm_BotNguyenADMM_Rates_lemma_15

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace
open NonconvexSplitting.Shared

namespace BotNguyenADMM.Rates.ProxMu1ZeroAux

abbrev E (n : ℕ) := BotNguyenADMM.KL.E n

/-! ### 1. Basic parameter facts and smoothness lemmas -/

lemma T0_pos {lam ρ : ℝ} (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) :
    0 < T0 lam ρ := by
  unfold T0
  split_ifs
  · positivity
  · have : 0 < 2 - ρ := by linarith
    positivity

lemma T1_nonneg {lam ρ r : ℝ} (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) (hr : 0 < r) :
    0 ≤ T1 lam ρ r := by
  unfold T1
  split_ifs with h
  · have : 0 ≤ 1 - ρ := by linarith
    positivity
  · have : 0 ≤ ρ - 1 := by linarith
    have : 0 < 2 - ρ := by linarith
    positivity

lemma L_pos_of_A2 {n m : ℕ} {v : BotNguyenADMM.KL.Variant} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₁ μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 v g h A L r ρ lam μ₁ μ₂ M₁ M₂) : 0 < L := by
  have hT0 := T0_pos hA2.lam_pos hA2.ρ_pos hA2.ρ_lt_two
  have hL4 := hA2.L_pos
  by_contra hc
  push Not at hc
  nlinarith

lemma M1_eq_zero {n m : ℕ} {v : BotNguyenADMM.KL.Variant} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 v g h A L r ρ lam 0 μ₂ M₁ M₂) (k : ℕ) : M₁ k = 0 :=
  norm_le_zero_iff.mp (hA2.M₁_bdd k)

lemma C1_prox_zero (L lam ρ r : ℝ) : C1 .prox L 0 lam ρ r = 0 := by
  simp [C1]

lemma metric_79_zero {n m : ℕ} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 .prox g h A L r ρ lam 0 μ₂ M₁ M₂) (w : E n) :
    (L + 8 * L ^ 2 * T0 lam ρ / r) * ‖w‖ ^ 2 ≤ r * ‖A w‖ ^ 2 := by
  have h79 := hA2.metric_79 0 w
  simp only [M1_eq_zero hA2 0, zero_apply, inner_zero_left, mul_zero, zero_add] at h79
  have hcm : CMprime .prox L 0 lam ρ = 8 * L ^ 2 * T0 lam ρ := by
    simp [CMprime]
  rwa [hcm] at h79

lemma T_ineq {lam ρ r : ℝ} (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) (hr : 0 < r)
    {E0 α ek : ℝ} (_hE : 0 ≤ E0) (_hα : 0 ≤ α) (hek0 : 0 ≤ ek)
    (hek : ek ≤ |1 - ρ| * E0 + ρ * α) :
    ek ^ 2 / (lam * ρ * r) + T1 lam ρ r * ek ^ 2 ≤
      T1 lam ρ r * E0 ^ 2 + T0 lam ρ / r * α ^ 2 := by
  unfold T0 T1
  split_ifs with h
  · rw [abs_of_nonneg (by linarith)] at hek
    have hsq : ek ^ 2 ≤ (1 - ρ) * E0 ^ 2 + ρ * α ^ 2 := by
      have h1 : ek ^ 2 ≤ ((1 - ρ) * E0 + ρ * α) ^ 2 := pow_le_pow_left₀ hek0 hek 2
      nlinarith [mul_nonneg (mul_nonneg hρ0.le (by linarith : (0 : ℝ) ≤ 1 - ρ)) (sq_nonneg (E0 - α))]
    have eL : ek ^ 2 / (lam * ρ * r) + (1 - ρ) / (lam * ρ ^ 2 * r) * ek ^ 2 =
        ek ^ 2 / (lam * ρ ^ 2 * r) := by field_simp; ring
    have eR : (1 - ρ) / (lam * ρ ^ 2 * r) * E0 ^ 2 + 1 / (lam * ρ) / r * α ^ 2 =
        ((1 - ρ) * E0 ^ 2 + ρ * α ^ 2) / (lam * ρ ^ 2 * r) := by field_simp
    rw [eL, eR]
    exact div_le_div_of_nonneg_right hsq (by positivity)
  · push Not at h
    rw [abs_of_neg (by linarith)] at hek
    have hb : 0 < 2 - ρ := by linarith
    have hek' : ek ≤ (ρ - 1) * E0 + ρ * α := by linarith
    have hsq : ek ^ 2 * (2 - ρ) ≤ (ρ - 1) * (2 - ρ) * E0 ^ 2 + ρ ^ 2 * α ^ 2 := by
      have h1 : ek ^ 2 ≤ ((ρ - 1) * E0 + ρ * α) ^ 2 := pow_le_pow_left₀ hek0 hek' 2
      have h3 : ((ρ - 1) * E0 + ρ * α) ^ 2 * (2 - ρ) ≤
          (ρ - 1) * (2 - ρ) * E0 ^ 2 + ρ ^ 2 * α ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ ρ - 1) hb.le)
          (sq_nonneg ((2 - ρ) * E0 - ρ * α))]
      nlinarith
    have eL : ek ^ 2 / (lam * ρ * r) + (ρ - 1) / (lam * (2 - ρ) * ρ * r) * ek ^ 2 =
        ek ^ 2 * (2 - ρ) / (lam * (2 - ρ) ^ 2 * ρ * r) := by field_simp; ring
    have eR : (ρ - 1) / (lam * (2 - ρ) * ρ * r) * E0 ^ 2 +
        ρ / (lam * (2 - ρ) ^ 2) / r * α ^ 2 =
        ((ρ - 1) * (2 - ρ) * E0 ^ 2 + ρ ^ 2 * α ^ 2) / (lam * (2 - ρ) ^ 2 * ρ * r) := by
      field_simp
    rw [eL, eR]
    exact div_le_div_of_nonneg_right hsq (by positivity)

lemma descent_abstract {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (G : V → V) (L : ℝ)
    (hder : ∀ p d : V, HasDerivAt (fun t : ℝ => f (p + t • d)) ⟪G p, d⟫ 0)
    (hL : ∀ p q, ‖G p - G q‖ ≤ L * ‖p - q‖) (p q : V) :
    f q ≤ f p + ⟪G p, q - p⟫ + L / 2 * ‖q - p‖ ^ 2 := by
  set d : V := q - p with hd
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (p + s • d)) ⟪G (p + t • d), d⟫ t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => f (p + t • d + s • d)) ⟪G (p + t • d), d⟫ (t + -t) := by
      simpa using hder (p + t • d) d
    have h2 := h1.comp_add_const t (-t)
    have h3 : (fun s : ℝ => f (p + t • d + (s + -t) • d)) = fun s : ℝ => f (p + s • d) := by
      funext s; congr 1; rw [add_smul, neg_smul]; abel
    rwa [h3] at h2
  set ψ : ℝ → ℝ := fun t => f (p + t • d) - f p - t * ⟪G p, d⟫ - L * ‖d‖ ^ 2 / 2 * t ^ 2 with hψ
  have hψ' : ∀ t : ℝ, HasDerivAt ψ (⟪G (p + t • d), d⟫ - ⟪G p, d⟫ - L * ‖d‖ ^ 2 * t) t := by
    intro t
    have h1 := (((hφ t).sub_const (f p)).sub ((hasDerivAt_id t).mul_const ⟪G p, d⟫)).sub
      ((hasDerivAt_pow 2 t).const_mul (L * ‖d‖ ^ 2 / 2))
    refine h1.congr_deriv ?_
    norm_num
    ring
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun t _ => (hψ' t).continuousAt.continuousWithinAt)
      (fun t _ => (hψ' t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [(hψ' t).deriv]
    have ht0 : 0 ≤ t := by rw [interior_Icc] at ht; exact ht.1.le
    have h1 : ⟪G (p + t • d) - G p, d⟫ ≤ L * (t * ‖d‖ ^ 2) := by
      calc ⟪G (p + t • d) - G p, d⟫ ≤ ‖G (p + t • d) - G p‖ * ‖d‖ := real_inner_le_norm _ _
        _ ≤ (L * ‖(p + t • d) - p‖) * ‖d‖ := by gcongr; exact hL _ _
        _ = L * (t * ‖d‖ ^ 2) := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]; ring
    rw [inner_sub_left] at h1
    nlinarith
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [hψ, one_smul, zero_smul, add_zero, zero_mul, sub_zero, one_mul, one_pow,
    zero_pow two_ne_zero, mul_zero] at h01
  have hpq : p + d = q := by rw [hd]; abel
  rw [hpq] at h01
  nlinarith

lemma h_hasDeriv {n : ℕ} (h : E n → ℝ) (hd : Differentiable ℝ h) (p d : E n) :
    HasDerivAt (fun t : ℝ => h (p + t • d)) ⟪gradient h p, d⟫ 0 := by
  have hℓ : HasDerivAt (fun t : ℝ => p + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add p
  have h1 := (hd (p + (0 : ℝ) • d)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hℓ
  have he : fderiv ℝ h p d = ⟪gradient h p, d⟫ := by
    unfold gradient
    rw [InnerProductSpace.toDual_symm_apply]
  simp only [zero_smul, add_zero] at h1
  rwa [he] at h1

lemma h_low {n : ℕ} (h : E n → ℝ) (L : ℝ) (hd : Differentiable ℝ h)
    (hlip : ∀ a b : E n, ‖gradient h a - gradient h b‖ ≤ L * ‖a - b‖) (p q : E n) :
    h p + ⟪gradient h p, q - p⟫ - L / 2 * ‖q - p‖ ^ 2 ≤ h q := by
  have h1 := descent_abstract (fun u => -h u) (fun u => -gradient h u) L
    (fun a d => by rw [inner_neg_left]; exact (h_hasDeriv h hd a d).neg)
    (fun a b => by
      rw [show -gradient h a - -gradient h b = -(gradient h a - gradient h b) by abel, norm_neg]
      exact hlip a b) p q
  simp only [inner_neg_left] at h1
  linarith

/-! ### 2. Algorithmic identities and Section 3 descent inequality -/

noncomputable def R3 {n m : ℕ} (h : E n → ℝ) (A : E n →L[ℝ] E m) (r : ℝ)
    (x : E n) (z y : E m) : ℝ :=
  h x + ⟪y, A x - z⟫ + r / 2 * ‖A x - z‖ ^ 2

noncomputable def Phi {n m : ℕ} (A : E n →L[ℝ] E m) (r : ℝ) (M₂ : E m →L[ℝ] E m)
    (xk : E n) (zk yk w : E m) : ℝ :=
  ⟪yk, A xk - w⟫ + r / 2 * ‖A xk - w‖ ^ 2 + 1 / 2 * ⟪M₂ (w - zk), w - zk⟫

/-- Real value of the Section 3 regularized augmented Lagrangian at `(x_{k+1}, z_{k+1}, y_{k+1}, x_k, y_k)`
when `v = prox` and `μ₁ = 0` (so `C₁ = 0`). -/
noncomputable def FR {n m : ℕ} (g : E m → EReal) (h : E n → ℝ) (A : E n →L[ℝ] E m)
    (r ρ lam : ℝ) (x : ℕ → E n) (z y : ℕ → E m) (k : ℕ) : ℝ :=
  (g (z (k + 1))).toReal + R3 h A r (x (k + 1)) (z (k + 1)) (y (k + 1)) +
    2 * T1 lam ρ r * ‖(ContinuousLinearMap.adjoint A) (y (k + 1) - y k)‖ ^ 2

lemma y_diff {n m : ℕ} {v : BotNguyenADMM.KL.Variant} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {r ρ : ℝ} {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun v g h A r ρ M₁ M₂ x z y) (k : ℕ) :
    y (k + 1) - y k = (ρ * r) • (A (x (k + 1)) - z (k + 1)) := by
  rw [(hrun k).2.2]; abel

lemma res_norm {n m : ℕ} {v : BotNguyenADMM.KL.Variant} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {r ρ : ℝ} {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    {x : ℕ → E n} {z y : ℕ → E m}
    (hρ : 0 < ρ) (hr : 0 < r) (hrun : IsRun v g h A r ρ M₁ M₂ x z y) (k : ℕ) :
    ‖A (x (k + 1)) - z (k + 1)‖ = ‖y (k + 1) - y k‖ / (ρ * r) := by
  have hpos : 0 < ρ * r := mul_pos hρ hr
  rw [y_diff hrun k, norm_smul, Real.norm_of_nonneg hpos.le, mul_div_cancel_left₀ _ hpos.ne']

lemma z_diff_bound {n m : ℕ} {v : BotNguyenADMM.KL.Variant} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {r ρ : ℝ} {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    {x : ℕ → E n} {z y : ℕ → E m}
    (hρ : 0 < ρ) (hr : 0 < r) (hrun : IsRun v g h A r ρ M₁ M₂ x z y) (k : ℕ) (hk : 1 ≤ k) :
    ‖z (k + 1) - z k‖ ≤ ‖A‖ * ‖x (k + 1) - x k‖ +
      ‖y (k + 1) - y k‖ / (ρ * r) + ‖y k - y (k - 1)‖ / (ρ * r) := by
  have e : z (k + 1) - z k = A (x (k + 1) - x k) -
      ((A (x (k + 1)) - z (k + 1)) - (A (x k) - z k)) := by
    rw [map_sub]; abel
  rw [e]
  have h1 := res_norm hρ hr hrun k
  have h2 := res_norm hρ hr hrun (k - 1)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at h2
  have h3 := norm_sub_le (A (x (k + 1)) - z (k + 1)) (A (x k) - z k)
  have h4 := A.le_opNorm (x (k + 1) - x k)
  have h5 := norm_sub_le (A (x (k + 1) - x k)) ((A (x (k + 1)) - z (k + 1)) - (A (x k) - z k))
  linarith

lemma gz_ne_top {n m : ℕ} {v : BotNguyenADMM.KL.Variant} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {r ρ : ℝ} {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    {x : ℕ → E n} {z y : ℕ → E m}
    (hprop : IsProperFn g) (hrun : IsRun v g h A r ρ M₁ M₂ x z y) (k : ℕ) :
    g (z (k + 1)) ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hprop.2
  intro htop
  have h1 := (hrun k).1 w
  unfold zObjective at h1
  rw [htop, EReal.top_add_coe] at h1
  have h2 := top_le_iff.1 h1
  rw [← EReal.coe_toReal hw (hprop.1 w), ← EReal.coe_add] at h2
  exact EReal.coe_ne_top _ h2

lemma gz_eq {n m : ℕ} {v : BotNguyenADMM.KL.Variant} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {r ρ : ℝ} {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    {x : ℕ → E n} {z y : ℕ → E m}
    (hprop : IsProperFn g) (hrun : IsRun v g h A r ρ M₁ M₂ x z y) (k : ℕ) :
    g (z (k + 1)) = ((g (z (k + 1))).toReal : EReal) :=
  (EReal.coe_toReal (gz_ne_top hprop hrun k) (hprop.1 _)).symm

lemma z_step {n m : ℕ} {v : BotNguyenADMM.KL.Variant} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {r ρ : ℝ} {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    {x : ℕ → E n} {z y : ℕ → E m}
    (hprop : IsProperFn g) (hrun : IsRun v g h A r ρ M₁ M₂ x z y) (k : ℕ)
    (w : E m) (gw : ℝ) (hgw : g w = (gw : EReal)) :
    (g (z (k + 1))).toReal + Phi A r (M₂ k) (x k) (z k) (y k) (z (k + 1)) ≤
      gw + Phi A r (M₂ k) (x k) (z k) (y k) w := by
  have h1 := (hrun k).1 w
  unfold zObjective at h1
  rw [hgw, gz_eq hprop hrun k, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  exact h1

lemma x_opt_prox_zero {n m : ℕ} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 .prox g h A L r ρ lam 0 μ₂ M₁ M₂)
    {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun .prox g h A r ρ M₁ M₂ x z y) (k : ℕ) :
    gradient h (x (k + 1)) +
      (ContinuousLinearMap.adjoint A) (y k + r • (A (x (k + 1)) - z (k + 1))) = 0 := by
  obtain ⟨_, hxmin, _⟩ := hrun k
  set u0 := x (k + 1)
  set G : E n := gradient h u0 + (ContinuousLinearMap.adjoint A) (y k + r • (A u0 - z (k + 1)))
  have hM0 := M1_eq_zero hA2 k
  have key : ∀ d : E n, ⟪G, d⟫ = 0 := by
    intro d
    have hℓ : HasDerivAt (fun t : ℝ => u0 + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add u0
    have hmin : IsLocalMin (fun t : ℝ => xObjective .prox h A r (M₁ k) (x k) (z (k + 1)) (y k)
        (u0 + t • d)) 0 := by
      refine Filter.Eventually.of_forall (fun t => ?_)
      simpa using hxmin (u0 + t • d)
    have hAℓ : HasDerivAt (fun t : ℝ => A (u0 + t • d) - z (k + 1)) (A d) 0 :=
      (A.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hℓ).sub_const (z (k + 1))
    have hq : HasDerivAt (fun t : ℝ => ‖A (u0 + t • d) - z (k + 1)‖ ^ 2)
        (2 * ⟪A u0 - z (k + 1), A d⟫) 0 := by
      simpa using hAℓ.norm_sq
    have hin : HasDerivAt (fun t : ℝ => ⟪y k, A (u0 + t • d) - z (k + 1)⟫) ⟪y k, A d⟫ 0 := by
      simpa using (hasDerivAt_const (0 : ℝ) (y k)).inner ℝ hAℓ
    have hmain := h_hasDeriv h hA2.h_diff u0 d
    have hall := (hmain.add hin).add (hq.const_mul (r / 2))
    have hxo : (fun t : ℝ => xObjective .prox h A r (M₁ k) (x k) (z (k + 1)) (y k) (u0 + t • d)) =
        ((fun t : ℝ => h (u0 + t • d)) + fun t : ℝ => ⟪y k, A (u0 + t • d) - z (k + 1)⟫) +
          fun t : ℝ => r / 2 * ‖A (u0 + t • d) - z (k + 1)‖ ^ 2 := by
      funext t
      simp [xObjective, hM0, Pi.add_apply]
    rw [hxo] at hmin
    have h0 := hmin.hasDerivAt_eq_zero hall
    have hGd : ⟪G, d⟫ = ⟪gradient h u0, d⟫ + ⟪y k, A d⟫ + r / 2 * (2 * ⟪A u0 - z (k + 1), A d⟫) := by
      simp only [G, inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
      ring
    rw [hGd]
    exact h0
  have h2 := key G
  rw [real_inner_self_eq_norm_sq] at h2
  exact norm_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h2)

lemma B_rec_prox_zero {n m : ℕ} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 .prox g h A L r ρ lam 0 μ₂ M₁ M₂)
    {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun .prox g h A r ρ M₁ M₂ x z y) (j : ℕ) :
    (ContinuousLinearMap.adjoint A) (y (j + 2) - y (j + 1)) =
      (1 - ρ) • (ContinuousLinearMap.adjoint A) (y (j + 1) - y j) -
        ρ • (gradient h (x (j + 2)) - gradient h (x (j + 1))) := by
  have hρ : ρ ≠ 0 := hA2.ρ_pos.ne'
  have hr : r ≠ 0 := hA2.r_pos.ne'
  have hQ : ∀ k, gradient h (x (k + 1)) + (ContinuousLinearMap.adjoint A) (y k) +
      (1 / ρ) • (ContinuousLinearMap.adjoint A) (y (k + 1) - y k) = 0 := by
    intro k
    have ho := x_opt_prox_zero hA2 hrun k
    have he : r • (A (x (k + 1)) - z (k + 1)) = (1 / ρ) • (y (k + 1) - y k) := by
      rw [y_diff hrun k, smul_smul]; congr 1; field_simp
    rw [map_add, he, map_smul] at ho
    simpa [add_assoc] using ho
  have e1 := hQ (j + 1)
  have e0 := hQ j
  set B1 := (ContinuousLinearMap.adjoint A) (y (j + 2) - y (j + 1))
  set B0 := (ContinuousLinearMap.adjoint A) (y (j + 1) - y j)
  set Q1 := gradient h (x (j + 2))
  set Q0 := gradient h (x (j + 1))
  set a1 := (ContinuousLinearMap.adjoint A) (y (j + 1))
  set a0 := (ContinuousLinearMap.adjoint A) (y j)
  have hB1 : B1 = -(ρ • Q1) - ρ • a1 := by
    have := congrArg (fun w => ρ • w) e1
    simp only [smul_add, smul_smul, smul_zero] at this
    rw [mul_one_div_cancel hρ, one_smul] at this
    rw [eq_sub_iff_add_eq, ← sub_eq_zero]
    rw [← this]; abel
  have hB0 : B0 = -(ρ • Q0) - ρ • a0 := by
    have := congrArg (fun w => ρ • w) e0
    simp only [smul_add, smul_smul, smul_zero] at this
    rw [mul_one_div_cancel hρ, one_smul] at this
    rw [eq_sub_iff_add_eq, ← sub_eq_zero]
    rw [← this]; abel
  have ha1 : a1 = a0 + B0 := by
    have hd : a1 - a0 = B0 := (map_sub _ _ _).symm
    rw [← hd]; abel
  have hρa0 : ρ • a0 = -(ρ • Q0) - B0 := by rw [hB0]; abel
  rw [hB1, ha1, smul_add, hρa0, sub_smul, one_smul, smul_sub]
  abel

lemma x_step_prox_zero {n m : ℕ} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 .prox g h A L r ρ lam 0 μ₂ M₁ M₂)
    {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun .prox g h A r ρ M₁ M₂ x z y) (k : ℕ) :
    R3 h A r (x (k + 1)) (z (k + 1)) (y k) +
      1 / 2 * (r * ‖A (x (k + 1) - x k)‖ ^ 2 - L * ‖x (k + 1) - x k‖ ^ 2) ≤
      R3 h A r (x k) (z (k + 1)) (y k) := by
  have hopt := x_opt_prox_zero hA2 hrun k
  set Δ := x (k + 1) - x k with hΔ
  set p := A (x (k + 1)) - z (k + 1) with hp
  have hq : A (x k) - z (k + 1) = p - A Δ := by rw [hp, hΔ, map_sub]; abel
  have hin := congrArg (fun w => ⟪w, Δ⟫) hopt
  simp only [inner_add_left, ContinuousLinearMap.adjoint_inner_left, inner_zero_left,
    real_inner_smul_left] at hin
  have hlow := h_low h L hA2.h_diff hA2.h_lipschitz (x (k + 1)) (x k)
  have he : x k - x (k + 1) = -Δ := by rw [hΔ]; abel
  rw [he, inner_neg_right, norm_neg] at hlow
  have L1 : R3 h A r (x k) (z (k + 1)) (y k) = h (x k) + (⟪y k, p⟫ - ⟪y k, A Δ⟫) +
      r / 2 * (‖p‖ ^ 2 - 2 * ⟪p, A Δ⟫ + ‖A Δ‖ ^ 2) := by
    unfold R3; rw [hq, inner_sub_right, norm_sub_sq_real]
  have L2 : R3 h A r (x (k + 1)) (z (k + 1)) (y k) = h (x (k + 1)) + ⟪y k, p⟫ + r / 2 * ‖p‖ ^ 2 := rfl
  rw [L1, L2]
  nlinarith

lemma y_step {n m : ℕ} {v : BotNguyenADMM.KL.Variant} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {r ρ : ℝ} {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    {x : ℕ → E n} {z y : ℕ → E m}
    (hρ : 0 < ρ) (hr : 0 < r) (hrun : IsRun v g h A r ρ M₁ M₂ x z y) (k : ℕ) :
    R3 h A r (x (k + 1)) (z (k + 1)) (y (k + 1)) =
      R3 h A r (x (k + 1)) (z (k + 1)) (y k) + ‖y (k + 1) - y k‖ ^ 2 / (ρ * r) := by
  have hpos : 0 < ρ * r := mul_pos hρ hr
  have hy := y_diff hrun k
  have h1 : ⟪y (k + 1) - y k, A (x (k + 1)) - z (k + 1)⟫ = ‖y (k + 1) - y k‖ ^ 2 / (ρ * r) := by
    have h2 : A (x (k + 1)) - z (k + 1) = (1 / (ρ * r)) • (y (k + 1) - y k) := by
      rw [hy, smul_smul, one_div_mul_cancel hpos.ne', one_smul]
    rw [h2, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have h2 : ⟪y (k + 1), A (x (k + 1)) - z (k + 1)⟫ =
      ⟪y k, A (x (k + 1)) - z (k + 1)⟫ + ⟪y (k + 1) - y k, A (x (k + 1)) - z (k + 1)⟫ := by
    rw [← inner_add_left]; congr 1; abel
  unfold R3
  rw [h2, h1]; ring

lemma Fk_succ_eq {n m : ℕ} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 .prox g h A L r ρ lam 0 μ₂ M₁ M₂)
    {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun .prox g h A r ρ M₁ M₂ x z y) (k : ℕ) :
    Fk .prox g h A L r ρ lam 0 x z y (k + 1) = (FR g h A r ρ lam x z y k : EReal) := by
  unfold Fk Freg augLag
  simp only [Nat.add_sub_cancel, Pt5.px, Pt5.pz, Pt5.py, Pt5.px', Pt5.py', pack5, C1_prox_zero,
    zero_mul, add_zero]
  rw [gz_eq hA2.g_proper hrun k, ← EReal.coe_add, ← EReal.coe_add]
  congr 1

lemma FR_descent {n m : ℕ} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 .prox g h A L r ρ lam 0 μ₂ M₁ M₂)
    {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun .prox g h A r ρ M₁ M₂ x z y) (k : ℕ) :
    FR g h A r ρ lam x z y (k + 1) +
      (2 * T0 lam ρ * L ^ 2 / r) * ‖x (k + 2) - x (k + 1)‖ ^ 2 +
      (1 / (ρ * r)) * ‖y (k + 2) - y (k + 1)‖ ^ 2 ≤
      FR g h A r ρ lam x z y k := by
  have hz := z_step hA2.g_proper hrun (k + 1) (z (k + 1)) _ (gz_eq hA2.g_proper hrun k)
  have hPhi1 : Phi A r (M₂ (k + 1)) (x (k + 1)) (z (k + 1)) (y (k + 1)) (z (k + 1)) =
      R3 h A r (x (k + 1)) (z (k + 1)) (y (k + 1)) - h (x (k + 1)) := by
    unfold Phi R3; simp; ring
  have hPhi2 : Phi A r (M₂ (k + 1)) (x (k + 1)) (z (k + 1)) (y (k + 1)) (z (k + 2)) =
      R3 h A r (x (k + 1)) (z (k + 2)) (y (k + 1)) - h (x (k + 1)) +
        1 / 2 * ⟪M₂ (k + 1) (z (k + 2) - z (k + 1)), z (k + 2) - z (k + 1)⟫ := by
    unfold Phi R3; ring
  rw [hPhi1, hPhi2] at hz
  have hM2 : 0 ≤ ⟪M₂ (k + 1) (z (k + 2) - z (k + 1)), z (k + 2) - z (k + 1)⟫ := by
    simpa using (hA2.M₂_psd (k + 1)).inner_nonneg_left (z (k + 2) - z (k + 1))
  have hx := x_step_prox_zero hA2 hrun (k + 1)
  have hy := y_step hA2.ρ_pos hA2.r_pos hrun (k + 1)
  have h79 := metric_79_zero hA2 (x (k + 2) - x (k + 1))
  have hlam := hA2.lam_le (y (k + 2) - y (k + 1))
  have hB := B_rec_prox_zero hA2 hrun k
  have hL := L_pos_of_A2 hA2
  have hek : ‖(ContinuousLinearMap.adjoint A) (y (k + 2) - y (k + 1))‖ ≤
      |1 - ρ| * ‖(ContinuousLinearMap.adjoint A) (y (k + 1) - y k)‖ +
        ρ * (L * ‖x (k + 2) - x (k + 1)‖) := by
    rw [hB]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hA2.ρ_pos]
    have hlip := mul_le_mul_of_nonneg_left (hA2.h_lipschitz (x (k + 2)) (x (k + 1))) hA2.ρ_pos.le
    linarith
  have hT := T_ineq hA2.lam_pos hA2.ρ_pos hA2.ρ_lt_two hA2.r_pos
    (norm_nonneg _) (mul_nonneg hL.le (norm_nonneg _)) (norm_nonneg _) hek
  have hdy : ‖y (k + 2) - y (k + 1)‖ ^ 2 / (ρ * r) ≤
      ‖(ContinuousLinearMap.adjoint A) (y (k + 2) - y (k + 1))‖ ^ 2 / (lam * ρ * r) := by
    have hρr : 0 < ρ * r := mul_pos hA2.ρ_pos hA2.r_pos
    rw [div_le_div_iff₀ hρr (mul_pos (mul_pos hA2.lam_pos hA2.ρ_pos) hA2.r_pos)]
    nlinarith
  have hT_alg : 2 * (T0 lam ρ / r * (L * ‖x (k + 2) - x (k + 1)‖) ^ 2) =
      (2 * T0 lam ρ * L ^ 2 / r) * ‖x (k + 2) - x (k + 1)‖ ^ 2 := by ring
  have h79_alg : 1 / 2 * (8 * L ^ 2 * T0 lam ρ / r * ‖x (k + 2) - x (k + 1)‖ ^ 2) =
      2 * ((2 * T0 lam ρ * L ^ 2 / r) * ‖x (k + 2) - x (k + 1)‖ ^ 2) := by ring
  have hdiv : 1 / (ρ * r) * ‖y (k + 2) - y (k + 1)‖ ^ 2 =
      ‖y (k + 2) - y (k + 1)‖ ^ 2 / (ρ * r) := by ring
  unfold FR
  simp only [show k + 1 + 1 = k + 2 from rfl] at hz hx hy ⊢
  linarith [hT, hdy, hT_alg, h79_alg, hdiv]

/-! ### 3. Convergence of `g(z^k)` and `E_k → 0` -/

lemma sq_diff_le {N : ℕ} (u v : E N) : ‖u‖ ^ 2 - ‖v‖ ^ 2 ≤ ‖u - v‖ * (‖u‖ + ‖v‖) := by
  have h1 : ‖u‖ - ‖v‖ ≤ ‖u - v‖ := norm_sub_norm_le u v
  have h2 : 0 ≤ ‖u‖ + ‖v‖ := by positivity
  nlinarith

lemma Phi_diff {n m : ℕ} (A : E n →L[ℝ] E m) (r μ₂ : ℝ) (hr : 0 ≤ r)
    (M₂ : E m →L[ℝ] E m) (hM₂ : ‖M₂‖ ≤ μ₂) (xk : E n) (zk yk a b : E m) :
    Phi A r M₂ xk zk yk a - Phi A r M₂ xk zk yk b ≤
      (‖yk‖ + r / 2 * (‖A xk - a‖ + ‖A xk - b‖) + μ₂ / 2 * (‖a - zk‖ + ‖b - zk‖)) * ‖a - b‖ := by
  unfold Phi
  have t1 : ⟪yk, A xk - a⟫ - ⟪yk, A xk - b⟫ ≤ ‖yk‖ * ‖a - b‖ := by
    rw [← inner_sub_right]
    have e : A xk - a - (A xk - b) = -(a - b) := by abel
    rw [e, inner_neg_right]
    have := neg_le_of_abs_le (abs_real_inner_le_norm yk (a - b))
    linarith
  have t2 : ‖A xk - a‖ ^ 2 - ‖A xk - b‖ ^ 2 ≤ ‖a - b‖ * (‖A xk - a‖ + ‖A xk - b‖) := by
    have := sq_diff_le (A xk - a) (A xk - b)
    have e : A xk - a - (A xk - b) = -(a - b) := by abel
    rwa [e, norm_neg] at this
  have t3 : ⟪M₂ (a - zk), a - zk⟫ - ⟪M₂ (b - zk), b - zk⟫ ≤
      μ₂ * ‖a - b‖ * (‖a - zk‖ + ‖b - zk‖) := by
    have gen : ∀ u w : E m, ⟪M₂ u, u⟫ - ⟪M₂ w, w⟫ = ⟪M₂ (u - w), u⟫ + ⟪M₂ w, u - w⟫ := by
      intro u w; rw [map_sub, inner_sub_left, inner_sub_right]; ring
    have e1 : (a - zk) - (b - zk) = a - b := by abel
    rw [gen (a - zk) (b - zk), e1]
    have h1 : ⟪M₂ (a - b), a - zk⟫ ≤ μ₂ * ‖a - b‖ * ‖a - zk‖ := by
      refine le_trans (real_inner_le_norm _ _) ?_
      have := (M₂.le_opNorm (a - b)).trans (mul_le_mul_of_nonneg_right hM₂ (norm_nonneg _))
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have h2 : ⟪M₂ (b - zk), a - b⟫ ≤ μ₂ * ‖a - b‖ * ‖b - zk‖ := by
      refine le_trans (real_inner_le_norm _ _) ?_
      have := (M₂.le_opNorm (b - zk)).trans (mul_le_mul_of_nonneg_right hM₂ (norm_nonneg _))
      nlinarith [norm_nonneg (a - b)]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left t2 (by positivity : (0 : ℝ) ≤ r / 2)]

lemma g_lim_limit {n m : ℕ} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 .prox g h A L r ρ lam 0 μ₂ M₁ M₂)
    {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun .prox g h A r ρ M₁ M₂ x z y)
    (R : ℝ) (hR : ∀ k, ‖x k‖ ≤ R ∧ ‖z k‖ ≤ R ∧ ‖y k‖ ≤ R)
    (zh : E m) (hzh : Tendsto z atTop (𝓝 zh)) :
    ∃ gs : ℝ, g zh = (gs : EReal) ∧
      Tendsto (fun k => (g (z (k + 1))).toReal) atTop (𝓝 gs) := by
  have hz1 : Tendsto (fun k => z (k + 1)) atTop (𝓝 zh) := hzh.comp (tendsto_add_atTop_nat 1)
  have hr := hA2.r_pos
  have hμ0 := hA2.μ₂_nonneg
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR 0).1
  set C : ℝ → ℝ := fun t => R + r / 2 * (2 * (‖A‖ * R) + t + R) + μ₂ / 2 * (t + 3 * R) with hC
  have hC0 : ∀ t, 0 ≤ t → 0 ≤ C t := fun t ht => by rw [hC]; positivity
  have hPd : ∀ k (a : E m), Phi A r (M₂ k) (x k) (z k) (y k) a -
      Phi A r (M₂ k) (x k) (z k) (y k) (z (k + 1)) ≤ C ‖a‖ * ‖a - z (k + 1)‖ := by
    intro k a
    refine le_trans (Phi_diff A r μ₂ hr.le (M₂ k) (hA2.M₂_bdd k) _ _ _ a (z (k + 1))) ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    obtain ⟨hx, _, hy⟩ := hR k
    have hz' := (hR (k + 1)).2.1
    have hzk := (hR k).2.1
    have hAx : ‖A (x k)‖ ≤ ‖A‖ * R := (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    have n1 : ‖A (x k) - a‖ ≤ ‖A‖ * R + ‖a‖ := (norm_sub_le _ _).trans (by linarith)
    have n2 : ‖A (x k) - z (k + 1)‖ ≤ ‖A‖ * R + R := (norm_sub_le _ _).trans (by linarith)
    have n3 : ‖a - z k‖ ≤ ‖a‖ + R := (norm_sub_le _ _).trans (by linarith)
    have n4 : ‖z (k + 1) - z k‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
    rw [hC]
    have := mul_le_mul_of_nonneg_left (add_le_add n1 n2) (by positivity : (0 : ℝ) ≤ r / 2)
    have := mul_le_mul_of_nonneg_left (add_le_add n3 n4) (by positivity : (0 : ℝ) ≤ μ₂ / 2)
    nlinarith
  obtain ⟨w0, hw0⟩ := hA2.g_proper.2
  have hg0 : g w0 = ((g w0).toReal : EReal) := (EReal.coe_toReal hw0 (hA2.g_proper.1 w0)).symm
  set U : ℝ := (g w0).toReal + C ‖w0‖ * (‖w0‖ + R) with hU
  have hup : ∀ k, (g (z (k + 1))).toReal ≤ U := by
    intro k
    have h1 := z_step hA2.g_proper hrun k w0 _ hg0
    have h2 := hPd k w0
    have h3 : ‖w0 - z (k + 1)‖ ≤ ‖w0‖ + R := (norm_sub_le _ _).trans (by linarith [(hR (k + 1)).2.1])
    have h4 := mul_le_mul_of_nonneg_left h3 (hC0 _ (norm_nonneg w0))
    rw [hU]; linarith
  have hle : g zh ≤ (U : EReal) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := (hz1.eventually (hA2.g_lsc zh (U : EReal) hcon)).exists
    rw [gz_eq hA2.g_proper hrun k] at hk
    have : U < (g (z (k + 1))).toReal := by exact_mod_cast hk
    linarith [hup k]
  have hne : g zh ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top U) hle
  set gs := (g zh).toReal
  have hgs' : g zh = (gs : EReal) := (EReal.coe_toReal hne (hA2.g_proper.1 zh)).symm
  refine ⟨gs, hgs', ?_⟩
  rw [tendsto_order]
  constructor
  · intro c hc
    have hc' : (c : EReal) < g zh := by rw [hgs']; exact_mod_cast hc
    filter_upwards [hz1.eventually (hA2.g_lsc zh (c : EReal) hc')] with k hk
    rw [gz_eq hA2.g_proper hrun k] at hk
    exact_mod_cast hk
  · intro c hc
    have hdist : Tendsto (fun k => C ‖zh‖ * ‖zh - z (k + 1)‖) atTop (𝓝 0) := by
      have h1 := (tendsto_iff_norm_sub_tendsto_zero.1 hz1).const_mul (C ‖zh‖)
      rw [mul_zero] at h1
      exact h1.congr (fun k => by rw [norm_sub_rev])
    filter_upwards [hdist.eventually (gt_mem_nhds (show (0 : ℝ) < c - gs by linarith))] with k hk
    have h1 := z_step hA2.g_proper hrun k zh gs hgs'
    have h2 := hPd k zh
    linarith

/-! ### 4. Explicit limiting subgradient of Section 3 `Freg` -/

lemma pack5_sub {n m : ℕ} (a a' : E n) (b b' c c' : E m) (d d' : E n) (e e' : E m) :
    pack5 a b c d e - pack5 a' b' c' d' e' =
      pack5 (a - a') (b - b') (c - c') (d - d') (e - e') := by
  simp only [pack5, ← WithLp.toLp_sub, Prod.mk_sub_mk]

lemma inner_pack5 {n m : ℕ} (a a' : E n) (b b' c c' : E m) (d d' : E n) (e e' : E m) :
    ⟪pack5 a b c d e, pack5 a' b' c' d' e'⟫ =
      ⟪a, a'⟫ + ⟪b, b'⟫ + ⟪c, c'⟫ + ⟪d, d'⟫ + ⟪e, e'⟫ := by
  simp [pack5, WithLp.prod_inner_apply]; ring

lemma normsq_pack5 {n m : ℕ} (a : E n) (b c : E m) (d : E n) (e : E m) :
    ‖pack5 a b c d e‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 + ‖e‖ ^ 2 := by
  simp [pack5, WithLp.prod_norm_sq_eq_of_L2]; ring

lemma pack5_eta {n m : ℕ} (u : Pt5 n m) :
    pack5 u.px u.pz u.py u.px' u.py' = u := rfl

lemma norm_pack5_le {n m : ℕ} (a : E n) (b c : E m) (d : E n) (e : E m) :
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

lemma reg_of_quad {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
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

lemma quad_bound (L a r μ dx dz dy dx' dy' : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hμ : 0 ≤ μ) (_hdx : 0 ≤ dx) (_hdz : 0 ≤ dz) (_hdy : 0 ≤ dy) :
    L / 2 * dx ^ 2 + dy * (a * dx + dz) + (r + μ) / 2 * dz ^ 2 ≤
      (L / 2 + a + 1 + (r + μ) / 2) * (dx ^ 2 + dz ^ 2 + dy ^ 2 + dx' ^ 2 + dy' ^ 2) := by
  nlinarith [sq_nonneg (dy - dx), sq_nonneg (dy - dz), mul_nonneg ha (sq_nonneg (dy - dx)),
    sq_nonneg dx', sq_nonneg dy', mul_nonneg hL (sq_nonneg dz), mul_nonneg hL (sq_nonneg dy),
    mul_nonneg ha (sq_nonneg dz), mul_nonneg (add_nonneg hr hμ) (sq_nonneg dx),
    mul_nonneg (add_nonneg hr hμ) (sq_nonneg dy), mul_nonneg hL (sq_nonneg dx'),
    mul_nonneg hL (sq_nonneg dy'), mul_nonneg ha (sq_nonneg dx'), mul_nonneg ha (sq_nonneg dy'),
    mul_nonneg (add_nonneg hr hμ) (sq_nonneg dx'), mul_nonneg (add_nonneg hr hμ) (sq_nonneg dy'),
    mul_nonneg ha (sq_nonneg dy)]

noncomputable def Wpt {n m : ℕ} (x : ℕ → E n) (z y : ℕ → E m) (k : ℕ) : Pt5 n m :=
  pack5 (x (k + 1)) (z (k + 1)) (y (k + 1)) (x k) (y k)

noncomputable def Vsub {n m : ℕ} (h : E n → ℝ) (A : E n →L[ℝ] E m) (r ρ lam : ℝ)
    (M₂ : ℕ → E m →L[ℝ] E m) (x : ℕ → E n) (z y : ℕ → E m) (k : ℕ) : Pt5 n m :=
  let w := (ContinuousLinearMap.adjoint A) (y (k + 1) - y k)
  let t := T1 lam ρ r
  pack5
    (gradient h (x (k + 1)) +
      (ContinuousLinearMap.adjoint A) (y (k + 1) + r • (A (x (k + 1)) - z (k + 1))))
    ((y k + r • (A (x k) - z (k + 1)) - M₂ k (z (k + 1) - z k)) -
      (y (k + 1) + r • (A (x (k + 1)) - z (k + 1))))
    ((A (x (k + 1)) - z (k + 1)) + (4 * t) • A w)
    0
    (-((4 * t) • A w))

lemma Freg_pack5_zero {n m : ℕ} (g : E m → EReal) (h : E n → ℝ) (A : E n →L[ℝ] E m)
    (L r ρ lam : ℝ) (X : E n) (Z Y : E m) (X' : E n) (Y' : E m) :
    Freg .prox g h A L r ρ lam 0 (pack5 X Z Y X' Y') =
      g Z + ((R3 h A r X Z Y + 2 * T1 lam ρ r * ‖(ContinuousLinearMap.adjoint A) (Y - Y')‖ ^ 2 : ℝ) : EReal) := by
  unfold Freg augLag R3
  simp only [Pt5.px, Pt5.pz, Pt5.py, Pt5.px', Pt5.py', pack5, C1_prox_zero, zero_mul, add_zero]
  rw [add_assoc, ← EReal.coe_add]

lemma V_minorant {n m : ℕ} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 .prox g h A L r ρ lam 0 μ₂ M₁ M₂)
    {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun .prox g h A r ρ M₁ M₂ x z y) (k : ℕ) (u' : Pt5 n m) :
    Freg .prox g h A L r ρ lam 0 (Wpt x z y k) +
      ((⟪Vsub h A r ρ lam M₂ x z y k, u' - Wpt x z y k⟫ -
        (L / 2 + ‖A‖ + 1 + (r + μ₂) / 2) * ‖u' - Wpt x z y k‖ ^ 2 : ℝ) : EReal) ≤
      Freg .prox g h A L r ρ lam 0 u' := by
  rw [← pack5_eta u']
  generalize u'.px = X; generalize u'.pz = Z; generalize u'.py = Y
  generalize u'.px' = X'; generalize u'.py' = Y'
  have hFW : Freg .prox g h A L r ρ lam 0 (Wpt x z y k) = (FR g h A r ρ lam x z y k : EReal) :=
    Fk_succ_eq hA2 hrun k
  rw [hFW, Freg_pack5_zero]
  by_cases hgtop : g Z = ⊤
  · rw [hgtop, EReal.top_add_coe]; exact le_top
  set gZ := (g Z).toReal
  have hgZ : g Z = (gZ : EReal) := (EReal.coe_toReal hgtop (hA2.g_proper.1 Z)).symm
  rw [hgZ, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hz := z_step hA2.g_proper hrun k Z gZ hgZ
  obtain ⟨DX, rfl⟩ : ∃ DX, X = x (k + 1) + DX := ⟨X - x (k + 1), by abel⟩
  obtain ⟨DZ, rfl⟩ : ∃ DZ, Z = z (k + 1) + DZ := ⟨Z - z (k + 1), by abel⟩
  obtain ⟨DY, rfl⟩ : ∃ DY, Y = y (k + 1) + DY := ⟨Y - y (k + 1), by abel⟩
  obtain ⟨DX', rfl⟩ : ∃ DX', X' = x k + DX' := ⟨X' - x k, by abel⟩
  obtain ⟨DY', rfl⟩ : ∃ DY', Y' = y k + DY' := ⟨Y' - y k, by abel⟩
  unfold Wpt
  rw [pack5_sub, normsq_pack5]
  simp only [add_sub_cancel_left]
  set p := A (x (k + 1)) - z (k + 1) with hp
  set q := A DX - DZ with hq
  set w := (ContinuousLinearMap.adjoint A) (y (k + 1) - y k) with hw
  set s := (ContinuousLinearMap.adjoint A) (DY - DY') with hs
  set p0 := A (x k) - z (k + 1) with hp0
  set a := z (k + 1) - z k with ha
  have hsymm : ∀ u u' : E m, ⟪M₂ k u, u'⟫ = ⟪u, M₂ k u'⟫ :=
    fun u u' => (hA2.M₂_psd k).isSymmetric u u'
  have I1 : R3 h A r (x (k + 1) + DX) (z (k + 1) + DZ) (y (k + 1) + DY) =
      h (x (k + 1) + DX) + ⟪y (k + 1), p⟫ + ⟪y (k + 1), q⟫ + ⟪DY, p⟫ + ⟪DY, q⟫ +
        r / 2 * (‖p‖ ^ 2 + 2 * ⟪p, q⟫ + ‖q‖ ^ 2) := by
    have e : A (x (k + 1) + DX) - (z (k + 1) + DZ) = p + q := by rw [hp, hq, map_add]; abel
    unfold R3; rw [e, norm_add_sq_real, inner_add_left, inner_add_right, inner_add_right]; ring
  have I2 : R3 h A r (x (k + 1)) (z (k + 1)) (y (k + 1)) =
      h (x (k + 1)) + ⟪y (k + 1), p⟫ + r / 2 * ‖p‖ ^ 2 := rfl
  have I3 : ‖(ContinuousLinearMap.adjoint A) (y (k + 1) + DY - (y k + DY'))‖ ^ 2 =
      ‖w‖ ^ 2 + 2 * (⟪A w, DY⟫ - ⟪A w, DY'⟫) + ‖s‖ ^ 2 := by
    have e : (ContinuousLinearMap.adjoint A) (y (k + 1) + DY - (y k + DY')) = w + s := by
      rw [hw, hs, ← map_add]; congr 1; abel
    rw [e, norm_add_sq_real, hs, ContinuousLinearMap.adjoint_inner_right, inner_sub_right]
  have I5 : ⟪Vsub h A r ρ lam M₂ x z y k, pack5 DX DZ DY DX' DY'⟫ =
      ⟪gradient h (x (k + 1)), DX⟫ + ⟪y (k + 1), q⟫ + r * ⟪p, q⟫ +
        (⟪y k, DZ⟫ + r * ⟪p0, DZ⟫ - ⟪M₂ k a, DZ⟫) + ⟪p, DY⟫ +
        4 * T1 lam ρ r * ⟪A w, DY⟫ - 4 * T1 lam ρ r * ⟪A w, DY'⟫ := by
    unfold Vsub
    dsimp only
    simp only [← hp, ← hp0, ← ha, ← hw]
    rw [inner_pack5]
    simp only [inner_add_left, inner_sub_left, inner_neg_left, inner_zero_left,
      real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left, hq, inner_sub_right]
    ring
  have I6 : Phi A r (M₂ k) (x k) (z k) (y k) (z (k + 1) + DZ) =
      Phi A r (M₂ k) (x k) (z k) (y k) (z (k + 1)) - ⟪y k, DZ⟫ - r * ⟪p0, DZ⟫ +
        r / 2 * ‖DZ‖ ^ 2 + ⟪M₂ k a, DZ⟫ + 1 / 2 * ⟪M₂ k DZ, DZ⟫ := by
    have e1 : A (x k) - (z (k + 1) + DZ) = p0 - DZ := by rw [hp0]; abel
    have e2 : z (k + 1) + DZ - z k = a + DZ := by rw [ha]; abel
    have e3 : ⟪M₂ k (a + DZ), a + DZ⟫ = ⟪M₂ k a, a⟫ + 2 * ⟪M₂ k a, DZ⟫ + ⟪M₂ k DZ, DZ⟫ := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsymm DZ a,
        real_inner_comm (M₂ k a) DZ]
      ring
    unfold Phi
    rw [e1, e2, e3, ← hp0, ← ha, inner_sub_right, norm_sub_sq_real]
    ring
  have B1 := h_low h L hA2.h_diff hA2.h_lipschitz (x (k + 1)) (x (k + 1) + DX)
  simp only [add_sub_cancel_left] at B1
  have hqn : ‖q‖ ≤ ‖A‖ * ‖DX‖ + ‖DZ‖ := by
    rw [hq]; exact (norm_sub_le _ _).trans (by gcongr; exact A.le_opNorm DX)
  have B2 : -(‖DY‖ * (‖A‖ * ‖DX‖ + ‖DZ‖)) ≤ ⟪DY, q⟫ := by
    have h1 := neg_le_of_abs_le (abs_real_inner_le_norm DY q)
    have h2 : ‖DY‖ * ‖q‖ ≤ ‖DY‖ * (‖A‖ * ‖DX‖ + ‖DZ‖) := by gcongr
    linarith
  have B3 : ⟪M₂ k DZ, DZ⟫ ≤ μ₂ * ‖DZ‖ ^ 2 := by
    calc ⟪M₂ k DZ, DZ⟫ ≤ ‖M₂ k DZ‖ * ‖DZ‖ := real_inner_le_norm _ _
      _ ≤ (‖M₂ k‖ * ‖DZ‖) * ‖DZ‖ := by gcongr; exact (M₂ k).le_opNorm DZ
      _ ≤ (μ₂ * ‖DZ‖) * ‖DZ‖ := by gcongr; exact hA2.M₂_bdd k
      _ = μ₂ * ‖DZ‖ ^ 2 := by ring
  have B5 := quad_bound L ‖A‖ r μ₂ ‖DX‖ ‖DZ‖ ‖DY‖ ‖DX'‖ ‖DY'‖ (L_pos_of_A2 hA2).le
    (norm_nonneg _) hA2.r_pos.le hA2.μ₂_nonneg (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have hT1 := T1_nonneg hA2.lam_pos hA2.ρ_pos hA2.ρ_lt_two hA2.r_pos
  have B4a : 0 ≤ 2 * T1 lam ρ r * ‖s‖ ^ 2 := by positivity
  have B4c : 0 ≤ r / 2 * ‖q‖ ^ 2 := mul_nonneg (div_nonneg hA2.r_pos.le two_pos.le) (sq_nonneg _)
  rw [I6] at hz
  rw [I1, I3, I5]
  unfold FR
  rw [I2]
  simp only [← hw]
  have hc1 := real_inner_comm DY p
  linarith [hz, B1, B2, B3, B5, B4a, B4c, hc1]

lemma V_lim {n m : ℕ} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 .prox g h A L r ρ lam 0 μ₂ M₁ M₂)
    {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun .prox g h A r ρ M₁ M₂ x z y) (k : ℕ) :
    Vsub h A r ρ lam M₂ x z y k ∈
      LimitingSubdiff (Freg .prox g h A L r ρ lam 0) (Wpt x z y k) := by
  have hreg : IsRegularSubgrad (Freg .prox g h A L r ρ lam 0) (Wpt x z y k)
      (Vsub h A r ρ lam M₂ x z y k) := by
    refine reg_of_quad _ _ _ (L / 2 + ‖A‖ + 1 + (r + μ₂) / 2)
      (by have := L_pos_of_A2 hA2; have := hA2.r_pos; have := hA2.μ₂_nonneg; positivity) ?_
      (V_minorant hA2 hrun k)
    have hFW : Freg .prox g h A L r ρ lam 0 (Wpt x z y k) = (FR g h A r ρ lam x z y k : EReal) :=
      Fk_succ_eq hA2 hrun k
    rw [hFW]; exact EReal.coe_ne_top _
  exact ⟨hreg.1, fun _ => Wpt x z y k, fun _ => Vsub h A r ρ lam M₂ x z y k,
    tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds, fun _ => hreg⟩

lemma V_norm_bound {n m : ℕ} {g : E m → EReal} {h : E n → ℝ}
    {A : E n →L[ℝ] E m} {L r ρ lam μ₂ : ℝ}
    {M₁ : ℕ → E n →L[ℝ] E n} {M₂ : ℕ → E m →L[ℝ] E m}
    (hA2 : Assumption2 .prox g h A L r ρ lam 0 μ₂ M₁ M₂)
    {x : ℕ → E n} {z y : ℕ → E m}
    (hrun : IsRun .prox g h A r ρ M₁ M₂ x z y) :
    ∃ M : ℝ, 0 < M ∧ ∀ k ≥ 1,
      ‖Vsub h A r ρ lam M₂ x z y k‖ ≤
        M * (‖x (k + 1) - x k‖ + ‖y (k + 1) - y k‖ + ‖y k - y (k - 1)‖) := by
  have hr := hA2.r_pos
  have hρ := hA2.ρ_pos
  have hpos : 0 < ρ * r := mul_pos hρ hr
  have hμ2 := hA2.μ₂_nonneg
  have hT1 := T1_nonneg hA2.lam_pos hρ hA2.ρ_lt_two hr
  set c1 : ℝ := (r + μ₂) * ‖A‖
  set c2 : ℝ := ‖ContinuousLinearMap.adjoint A‖ + 1 + (1 + μ₂) / (ρ * r) +
    8 * T1 lam ρ r * ‖A‖ * ‖ContinuousLinearMap.adjoint A‖
  set c3 : ℝ := μ₂ / (ρ * r)
  set M : ℝ := max c1 c2
  have hc2_ge1 : 1 ≤ c2 := by
    have : 0 ≤ ‖ContinuousLinearMap.adjoint A‖ := norm_nonneg _
    have : 0 ≤ (1 + μ₂) / (ρ * r) := by positivity
    have : 0 ≤ 8 * T1 lam ρ r * ‖A‖ * ‖ContinuousLinearMap.adjoint A‖ := by positivity
    linarith
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (hc2_ge1.trans (le_max_right _ _))
  have hc3_le : c3 ≤ c2 := by
    have h1 : μ₂ / (ρ * r) ≤ (1 + μ₂) / (ρ * r) := div_le_div_of_nonneg_right (by linarith) hpos.le
    have : 0 ≤ ‖ContinuousLinearMap.adjoint A‖ := norm_nonneg _
    have : 0 ≤ 8 * T1 lam ρ r * ‖A‖ * ‖ContinuousLinearMap.adjoint A‖ := by positivity
    linarith
  refine ⟨M, hM_pos, fun k hk => ?_⟩
  have hopt := x_opt_prox_zero hA2 hrun k
  set w := (ContinuousLinearMap.adjoint A) (y (k + 1) - y k)
  set Δx := x (k + 1) - x k
  set Δy := y (k + 1) - y k
  set Δy' := y k - y (k - 1)
  have hVx : gradient h (x (k + 1)) +
      (ContinuousLinearMap.adjoint A) (y (k + 1) + r • (A (x (k + 1)) - z (k + 1))) = w := by
    have e : (ContinuousLinearMap.adjoint A) (y (k + 1) + r • (A (x (k + 1)) - z (k + 1))) =
        (ContinuousLinearMap.adjoint A) (y k + r • (A (x (k + 1)) - z (k + 1))) + w := by
      rw [← map_add]; congr 1; abel
    rw [e]
    have e2 : (ContinuousLinearMap.adjoint A) (y k + r • (A (x (k + 1)) - z (k + 1))) =
        -gradient h (x (k + 1)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hopt
    rw [e2]; abel
  have hVz : (y k + r • (A (x k) - z (k + 1)) - M₂ k (z (k + 1) - z k)) -
      (y (k + 1) + r • (A (x (k + 1)) - z (k + 1))) =
      -Δy - r • A Δx - M₂ k (z (k + 1) - z k) := by
    simp only [Δx, Δy, map_sub, smul_sub]; abel
  have hwn : ‖w‖ ≤ ‖ContinuousLinearMap.adjoint A‖ * ‖Δy‖ :=
    (ContinuousLinearMap.adjoint A).le_opNorm Δy
  have hAwn : ‖A w‖ ≤ ‖A‖ * (‖ContinuousLinearMap.adjoint A‖ * ‖Δy‖) :=
    (A.le_opNorm w).trans (mul_le_mul_of_nonneg_left hwn (norm_nonneg A))
  have hdz := z_diff_bound hρ hr hrun k hk
  have hM2n : ‖M₂ k (z (k + 1) - z k)‖ ≤ μ₂ * ‖z (k + 1) - z k‖ :=
    ((M₂ k).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA2.M₂_bdd k) (norm_nonneg _))
  have hVzn : ‖-Δy - r • A Δx - M₂ k (z (k + 1) - z k)‖ ≤
      ‖Δy‖ + r * (‖A‖ * ‖Δx‖) + μ₂ * ‖z (k + 1) - z k‖ := by
    have h1 := norm_sub_le (-Δy - r • A Δx) (M₂ k (z (k + 1) - z k))
    have h2 := norm_sub_le (-Δy) (r • A Δx)
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hr.le] at h2
    have h3 := mul_le_mul_of_nonneg_left (A.le_opNorm Δx) hr.le
    linarith
  have hVyn : ‖(A (x (k + 1)) - z (k + 1)) + (4 * T1 lam ρ r) • A w‖ ≤
      ‖Δy‖ / (ρ * r) + 4 * T1 lam ρ r * (‖A‖ * (‖ContinuousLinearMap.adjoint A‖ * ‖Δy‖)) := by
    refine (norm_add_le _ _).trans ?_
    rw [res_norm hρ hr hrun k, norm_smul, Real.norm_of_nonneg (by positivity)]
    gcongr
  have hVy'n : ‖-((4 * T1 lam ρ r) • A w)‖ ≤
      4 * T1 lam ρ r * (‖A‖ * (‖ContinuousLinearMap.adjoint A‖ * ‖Δy‖)) := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
    gcongr
  have htot : ‖Vsub h A r ρ lam M₂ x z y k‖ ≤
      ‖w‖ + ‖-Δy - r • A Δx - M₂ k (z (k + 1) - z k)‖ +
        ‖(A (x (k + 1)) - z (k + 1)) + (4 * T1 lam ρ r) • A w‖ + ‖(0 : E n)‖ +
        ‖-((4 * T1 lam ρ r) • A w)‖ := by
    unfold Vsub; dsimp only; rw [hVx, hVz]
    exact norm_pack5_le _ _ _ _ _
  rw [norm_zero] at htot
  have hdz_mul : μ₂ * ‖z (k + 1) - z k‖ ≤
      μ₂ * (‖A‖ * ‖Δx‖ + ‖Δy‖ / (ρ * r) + ‖Δy'‖ / (ρ * r)) :=
    mul_le_mul_of_nonneg_left hdz hμ2
  have hlin : ‖Vsub h A r ρ lam M₂ x z y k‖ ≤ c1 * ‖Δx‖ + c2 * ‖Δy‖ + c3 * ‖Δy'‖ := by
    have hring1 : c1 * ‖Δx‖ + c2 * ‖Δy‖ + c3 * ‖Δy'‖ =
        ‖ContinuousLinearMap.adjoint A‖ * ‖Δy‖ +
          (‖Δy‖ + r * (‖A‖ * ‖Δx‖) + μ₂ * (‖A‖ * ‖Δx‖ + ‖Δy‖ / (ρ * r) + ‖Δy'‖ / (ρ * r))) +
          (‖Δy‖ / (ρ * r) + 4 * T1 lam ρ r * (‖A‖ * (‖ContinuousLinearMap.adjoint A‖ * ‖Δy‖))) +
          4 * T1 lam ρ r * (‖A‖ * (‖ContinuousLinearMap.adjoint A‖ * ‖Δy‖)) := by
      simp only [c1, c2, c3]; ring
    linarith
  have hm1 : c1 ≤ M := le_max_left _ _
  have hm2 : c2 ≤ M := le_max_right _ _
  have hm3 : c3 ≤ M := hc3_le.trans hm2
  nlinarith [norm_nonneg Δx, norm_nonneg Δy, norm_nonneg Δy']

/-! ### 5. Concavity of `phiLoj`, telescoping sums, and rate transfer helpers -/

lemma phiLoj_nonneg {CL θ s : ℝ} (hCL : 0 < CL) (hθ1 : θ < 1) (hs : 0 ≤ s) :
    0 ≤ phiLoj CL θ s := by
  unfold phiLoj
  have h1θ : 0 < 1 - θ := by linarith
  have := Real.rpow_nonneg hs (1 - θ)
  positivity

lemma phiLoj_mono {CL θ a b : ℝ} (hCL : 0 < CL) (hθ1 : θ < 1) (hb : 0 ≤ b) (hba : b ≤ a) :
    phiLoj CL θ b ≤ phiLoj CL θ a := by
  unfold phiLoj
  have h1θ : 0 < 1 - θ := by linarith
  have hp : b ^ (1 - θ) ≤ a ^ (1 - θ) := Real.rpow_le_rpow hb hba h1θ.le
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hCL.le) h1θ.le

lemma phiLoj_concave_diff {CL θ a b : ℝ} (hCL : 0 < CL) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : 0 < a) :
    CL * a ^ (-θ) * (a - b) ≤ phiLoj CL θ a - phiLoj CL θ b := by
  have h1θ : 0 < 1 - θ := by linarith
  set f : ℝ → ℝ := fun t => t ^ (1 - θ) - (1 - θ) * a ^ (-θ) * t with hf
  have hcont : ContinuousOn f (Set.Icc b a) := by
    have h1 : Continuous (fun t : ℝ => t ^ (1 - θ)) :=
      continuous_id.rpow_const (fun _ => Or.inr h1θ.le)
    have h2 : Continuous (fun t : ℝ => (1 - θ) * a ^ (-θ) * t) := continuous_const.mul continuous_id
    exact (h1.sub h2).continuousOn
  have hder : ∀ t ∈ interior (Set.Icc b a),
      HasDerivAt f ((1 - θ) * t ^ (-θ) - (1 - θ) * a ^ (-θ)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have htpos : 0 < t := lt_of_le_of_lt hb ht.1
    have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - θ)) ((1 - θ) * t ^ ((1 - θ) - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl htpos.ne')
    have he : (1 - θ) - 1 = -θ := by ring
    rw [he] at h1
    have h2 : HasDerivAt (fun x : ℝ => (1 - θ) * a ^ (-θ) * x) ((1 - θ) * a ^ (-θ)) t := by
      simpa using (hasDerivAt_id t).const_mul ((1 - θ) * a ^ (-θ))
    exact h1.sub h2
  have hmono : MonotoneOn f (Set.Icc b a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc b a) hcont
      (fun t ht => (hder t ht).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [(hder t ht).deriv]
    rw [interior_Icc] at ht
    have htpos : 0 < t := lt_of_le_of_lt hb ht.1
    have hpow : t ^ θ ≤ a ^ θ := Real.rpow_le_rpow htpos.le ht.2.le hθ0
    have hinv : a ^ (-θ) ≤ t ^ (-θ) := by
      rw [Real.rpow_neg ha.le, Real.rpow_neg htpos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos htpos θ) hpow
    nlinarith
  have hfb : f b ≤ f a := hmono (Set.left_mem_Icc.2 hba) (Set.right_mem_Icc.2 hba) hba
  have hdiff : (1 - θ) * a ^ (-θ) * (a - b) ≤ a ^ (1 - θ) - b ^ (1 - θ) := by
    simp only [hf] at hfb; linarith
  have hmul : CL / (1 - θ) * ((1 - θ) * a ^ (-θ) * (a - b)) ≤
      CL / (1 - θ) * (a ^ (1 - θ) - b ^ (1 - θ)) :=
    mul_le_mul_of_nonneg_left hdiff (div_nonneg hCL.le h1θ.le)
  have eL : CL / (1 - θ) * ((1 - θ) * a ^ (-θ) * (a - b)) = CL * a ^ (-θ) * (a - b) := by
    field_simp
  have eR : CL / (1 - θ) * (a ^ (1 - θ) - b ^ (1 - θ)) = phiLoj CL θ a - phiLoj CL θ b := by
    unfold phiLoj; ring
  linarith

lemma tele_sum_step (s P : ℕ → ℝ) (C : ℝ) (m : ℕ)
    (hs : ∀ k, 0 ≤ s k) (hP : ∀ k, 0 ≤ P k) (hC : 0 ≤ C)
    (hstep : ∀ i : ℕ, s (m + i + 2) ≤ 1 / 4 * s (m + i + 1) + 1 / 4 * s (m + i) +
      C * (P (m + i + 2) - P (m + i + 3))) (N : ℕ) :
    ∑ i ∈ Finset.range N, s (m + i + 2) ≤
      s (m + 1) + 1 / 2 * s m + 2 * C * P (m + 2) := by
  have hsum : ∑ i ∈ Finset.range N, s (m + i + 2) ≤
      ∑ i ∈ Finset.range N, (1 / 4 * s (m + i + 1) + 1 / 4 * s (m + i) +
        C * (P (m + i + 2) - P (m + i + 3))) :=
    Finset.sum_le_sum (fun i _ => hstep i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hsum
  have htele : ∑ i ∈ Finset.range N, (P (m + i + 2) - P (m + i + 3)) =
      P (m + 2) - P (m + N + 2) := by
    have h1 := Finset.sum_range_sub' (fun i => P (m + i + 2)) N
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
  have hshift1 : ∑ i ∈ Finset.range N, s (m + i + 1) ≤
      s (m + 1) + ∑ i ∈ Finset.range N, s (m + i + 2) := by
    have h1 : ∑ i ∈ Finset.range N, s (m + i + 1) ≤ ∑ i ∈ Finset.range (N + 1), s (m + i + 1) := by
      rw [Finset.sum_range_succ]; linarith [hs (m + N + 1)]
    have h2 : ∑ i ∈ Finset.range (N + 1), s (m + i + 1) =
        s (m + 1) + ∑ i ∈ Finset.range N, s (m + i + 2) := by
      rw [Finset.sum_range_succ']
      simp only [add_zero]
      have : (fun i => s (m + (i + 1) + 1)) = fun i => s (m + i + 2) := funext fun i => rfl
      rw [this, add_comm]
    linarith
  have hshift2 : ∑ i ∈ Finset.range N, s (m + i) ≤
      s m + s (m + 1) + ∑ i ∈ Finset.range N, s (m + i + 2) := by
    have h1 : ∑ i ∈ Finset.range N, s (m + i) ≤ ∑ i ∈ Finset.range (N + 2), s (m + i) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith [hs (m + N), hs (m + (N + 1))]
    have h2 : ∑ i ∈ Finset.range (N + 2), s (m + i) =
        s m + s (m + 1) + ∑ i ∈ Finset.range N, s (m + i + 2) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [add_zero, zero_add]
      have : (fun i => s (m + (i + 1 + 1))) = fun i => s (m + i + 2) := funext fun i => rfl
      rw [this]; ring
    linarith
  have hPnonneg : 0 ≤ P (m + N + 2) := hP _
  have hCtel : C * (P (m + 2) - P (m + N + 2)) ≤ C * P (m + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  rw [htele] at hsum
  linarith

lemma norm_sub_le_sum_steps {X : Type*} [NormedAddCommGroup X] (u : ℕ → X) (k N : ℕ) :
    ‖u k - u (k + N)‖ ≤ ∑ i ∈ Finset.range N, ‖u (k + i + 1) - u (k + i)‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have e : u k - u (k + (N + 1)) = (u k - u (k + N)) - (u (k + N + 1) - u (k + N)) := by
      have : k + (N + 1) = k + N + 1 := by omega
      rw [this]; abel
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith)

lemma norm_sub_limit_le {X : Type*} [NormedAddCommGroup X] (u : ℕ → X) (uh : X)
    (hu : Tendsto u atTop (𝓝 uh)) (k : ℕ) (B : ℝ)
    (hB : ∀ N : ℕ, ∑ i ∈ Finset.range N, ‖u (k + i + 1) - u (k + i)‖ ≤ B) :
    ‖u k - uh‖ ≤ B := by
  have ht : Tendsto (fun N => ‖u k - u (k + N)‖) atTop (𝓝 ‖u k - uh‖) := by
    have h1 : Tendsto (fun N => u (k + N)) atTop (𝓝 uh) := by
      have := hu.comp (tendsto_add_atTop_nat k)
      exact this.congr (fun N => by simp [Nat.add_comm])
    exact ((tendsto_const_nhds.sub h1).norm)
  exact le_of_tendsto ht (Filter.Eventually.of_forall (fun N => (norm_sub_le_sum_steps u k N).trans (hB N)))

lemma key_max_bound (CL θ C s u w : ℝ) (hCL : 0 < CL) (hθ : θ < 1) (hC : 0 < C)
    (hs : 0 ≤ s) (hsu : s ≤ C * u) (hu : 0 ≤ u) (h1 : Real.sqrt u ≤ w)
    (h2 : u ^ (1 - θ) ≤ w) :
    max (Real.sqrt s) (phiLoj CL θ s) ≤
      max (Real.sqrt C) (CL * C ^ (1 - θ) / (1 - θ)) * w := by
  have hw : 0 ≤ w := le_trans (Real.sqrt_nonneg u) h1
  have h1θ : 0 < 1 - θ := by linarith
  apply max_le
  · calc Real.sqrt s ≤ Real.sqrt (C * u) := Real.sqrt_le_sqrt hsu
      _ = Real.sqrt C * Real.sqrt u := Real.sqrt_mul hC.le u
      _ ≤ Real.sqrt C * w := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hw
  · unfold phiLoj
    have hp : s ^ (1 - θ) ≤ (C * u) ^ (1 - θ) := Real.rpow_le_rpow hs hsu h1θ.le
    rw [Real.mul_rpow hC.le hu] at hp
    have hCp : 0 ≤ C ^ (1 - θ) := Real.rpow_nonneg hC.le _
    calc CL * s ^ (1 - θ) / (1 - θ) ≤ CL * (C ^ (1 - θ) * u ^ (1 - θ)) / (1 - θ) := by
          apply div_le_div_of_nonneg_right _ h1θ.le
          exact mul_le_mul_of_nonneg_left hp hCL.le
      _ = (CL * C ^ (1 - θ) / (1 - θ)) * u ^ (1 - θ) := by ring
      _ ≤ (CL * C ^ (1 - θ) / (1 - θ)) * w := by
          apply mul_le_mul_of_nonneg_left h2
          exact div_nonneg (mul_nonneg hCL.le hCp) h1θ.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hw

lemma lin_aux (Q θ : ℝ) (k : ℕ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) (hθ : θ ≤ 1 / 2) :
    Real.sqrt (Q ^ k) ≤ Real.sqrt Q ^ k ∧ (Q ^ k) ^ (1 - θ) ≤ Real.sqrt Q ^ k := by
  have hs : Real.sqrt (Q ^ k) = Real.sqrt Q ^ k := by
    have e : Q ^ k = (Real.sqrt Q ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hQ0.le]
    rw [e, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]
  refine ⟨hs.le, ?_⟩
  rw [← hs, Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge (pow_pos hQ0 k) (pow_le_one₀ hQ0.le hQ1) (by linarith)

lemma sub_aux (t θ : ℝ) (ht : 1 ≤ t) (hθ1 : 1 / 2 < θ) (hθ2 : θ < 1) :
    Real.sqrt (t ^ (-(1 / (2 * θ - 1)))) ≤ t ^ (-((1 - θ) / (2 * θ - 1))) ∧
      (t ^ (-(1 / (2 * θ - 1)))) ^ (1 - θ) ≤ t ^ (-((1 - θ) / (2 * θ - 1))) := by
  have ht0 : 0 ≤ t := by linarith
  have hd : 0 < 2 * θ - 1 := by linarith
  constructor
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0]
    apply Real.rpow_le_rpow_of_exponent_le ht
    rw [neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  · rw [← Real.rpow_mul ht0]
    apply le_of_eq
    congr 1
    field_simp

lemma rpow_neg_shift (a b q : ℝ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (h : b ≤ 2 * a) :
    a ^ (-q) ≤ 2 ^ q * b ^ (-q) := by
  have h1 : b ^ q ≤ (2 * a) ^ q := Real.rpow_le_rpow hb.le h hq.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.le] at h1
  rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  have haq : 0 < a ^ q := Real.rpow_pos_of_pos ha q
  have hbq : 0 < b ^ q := Real.rpow_pos_of_pos hb q
  have h2 : (a ^ q)⁻¹ * (a ^ q * b ^ q) ≤ (2 ^ q * (b ^ q)⁻¹) * (a ^ q * b ^ q) := by
    have eL : (a ^ q)⁻¹ * (a ^ q * b ^ q) = b ^ q := by field_simp
    have eR : (2 ^ q * (b ^ q)⁻¹) * (a ^ q * b ^ q) = 2 ^ q * a ^ q := by field_simp
    rw [eL, eR]; exact h1
  exact le_of_mul_le_mul_right h2 (mul_pos haq hbq)

lemma rec_for_lemma15 {n m : ℕ} (x : ℕ → E n) (y : ℕ → E m) (e : ℕ → ℝ)
    (κ CL M θ : ℝ) (N₀ : ℕ) (hN₀ : 2 ≤ N₀)
    (hκ : 0 < κ) (hCL : 0 < CL) (hM : 0 < M)
    (he_nonneg : ∀ k, 0 ≤ e k) (he_anti : Antitone e)
    (he_desc : ∀ k ≥ 1, e (k + 1) + κ * (‖x (k + 1) - x k‖ ^ 2 + ‖y (k + 1) - y k‖ ^ 2) ≤ e k)
    (hLoj_at : ∀ k ≥ N₀ + 1, e k ≠ 0 →
      e k ^ θ ≤ CL * M * (‖x k - x (k - 1)‖ + ‖y k - y (k - 1)‖ + ‖y (k - 1) - y (k - 2)‖)) :
    ∀ k ≥ N₀ + 1,
      (κ / (3 * CL ^ 2 * M ^ 2)) * (if e k = 0 then 0 else e k ^ (2 * θ)) ≤ e (k - 2) - e k := by
  intro k hk
  split_ifs with hz
  · rw [mul_zero]
    have : e k ≤ e (k - 2) := he_anti (by omega)
    linarith
  · have hlj := hLoj_at k hk hz
    set a := ‖x k - x (k - 1)‖
    set b := ‖y k - y (k - 1)‖
    set c := ‖y (k - 1) - y (k - 2)‖
    have hsq : e k ^ (2 * θ) ≤ 3 * CL ^ 2 * M ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      have h1 : (e k ^ θ) ^ 2 ≤ (CL * M * (a + b + c)) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg (he_nonneg k) θ) hlj 2
      have h2 : (e k ^ θ) ^ 2 = e k ^ (2 * θ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (he_nonneg k)]
        congr 1; push_cast; ring
      have h3 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      rw [h2] at h1
      have h4 : (CL * M * (a + b + c)) ^ 2 = CL ^ 2 * M ^ 2 * (a + b + c) ^ 2 := by ring
      rw [h4] at h1
      have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ CL ^ 2 * M ^ 2)
      linarith
    have hd1 := he_desc (k - 1) (by omega)
    have hd2 := he_desc (k - 2) (by omega)
    have hk1 : k - 1 + 1 = k := by omega
    have hk2 : k - 2 + 1 = k - 1 := by omega
    rw [hk1] at hd1
    rw [hk2] at hd2
    have hsum_desc : κ * (a ^ 2 + b ^ 2 + c ^ 2) ≤ e (k - 2) - e k := by
      have h0 : 0 ≤ κ * ‖x (k - 1) - x (k - 2)‖ ^ 2 := by positivity
      linarith
    have hden : 0 < 3 * CL ^ 2 * M ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    calc κ * e k ^ (2 * θ) ≤ κ * (3 * CL ^ 2 * M ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq hκ.le
      _ = κ * (a ^ 2 + b ^ 2 + c ^ 2) * (3 * CL ^ 2 * M ^ 2) := by ring
      _ ≤ (e (k - 2) - e k) * (3 * CL ^ 2 * M ^ 2) :=
          mul_le_mul_of_nonneg_right hsum_desc hden.le

lemma iter_tail_bounds {n m : ℕ} (A : E n →L[ℝ] E m) (ρ r : ℝ) (hρr : 0 < ρ * r)
    (x : ℕ → E n) (z y : ℕ → E m) (xh : E n) (zh yh : E m)
    (hxh : Tendsto x atTop (𝓝 xh)) (hyh : Tendsto y atTop (𝓝 yh))
    (hzh_eq : zh = A xh) (hres : ∀ k, ‖A (x (k + 1)) - z (k + 1)‖ = ‖y (k + 1) - y k‖ / (ρ * r))
    (e : ℕ → ℝ) (κ CL M θ : ℝ) (N₀ : ℕ) (hN₀ : 2 ≤ N₀)
    (hκ : 0 < κ) (hCL : 0 < CL) (hM : 0 < M) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (he_nonneg : ∀ k, 0 ≤ e k) (he_anti : Antitone e)
    (he_desc : ∀ k ≥ 1, e (k + 1) + κ * (‖x (k + 1) - x k‖ ^ 2 + ‖y (k + 1) - y k‖ ^ 2) ≤ e k)
    (hLoj_at : ∀ k ≥ N₀ + 1, e k ≠ 0 →
      e k ^ θ ≤ CL * M * (‖x k - x (k - 1)‖ + ‖y k - y (k - 1)‖ + ‖y (k - 1) - y (k - 2)‖)) :
    ∃ cB : ℝ, 0 < cB ∧ ∀ k ≥ N₀ + 1,
      ‖x k - xh‖ ≤ cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) ∧
      ‖y k - yh‖ ≤ cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) ∧
      ‖z k - zh‖ ≤ (‖A‖ + 1 / (ρ * r)) *
        (cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2)))) := by
  set κh : ℝ := κ / 2 with hκhdef
  have hκh_pos : 0 < κh := by positivity
  set s : ℕ → ℝ := fun j => ‖x (j + 1) - x j‖ + ‖y (j + 1) - y j‖ with hsdef
  have hs_nonneg : ∀ j, 0 ≤ s j := fun j => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hs_sq_le : ∀ j ≥ 1, κh * s j ^ 2 ≤ e j - e (j + 1) := by
    intro j hj
    have hd := he_desc j hj
    have hcs : s j ^ 2 ≤ 2 * (‖x (j + 1) - x j‖ ^ 2 + ‖y (j + 1) - y j‖ ^ 2) := by
      simp only [hsdef]
      nlinarith [sq_nonneg (‖x (j + 1) - x j‖ - ‖y (j + 1) - y j‖)]
    calc κh * s j ^ 2
        ≤ κh * (2 * (‖x (j + 1) - x j‖ ^ 2 + ‖y (j + 1) - y j‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs hκh_pos.le
      _ = κ * (‖x (j + 1) - x j‖ ^ 2 + ‖y (j + 1) - y j‖ ^ 2) := by rw [hκhdef]; ring
      _ ≤ e j - e (j + 1) := by linarith
  have hs_le_sqrt : ∀ j ≥ 1, s j ≤ Real.sqrt (e j) / Real.sqrt κh := by
    intro j hj
    have h1 := hs_sq_le j hj
    have h2 : κh * s j ^ 2 ≤ e j := by linarith [he_nonneg (j + 1)]
    have h3 : (s j * Real.sqrt κh) ^ 2 ≤ (Real.sqrt (e j)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hκh_pos.le, Real.sq_sqrt (he_nonneg j)]
      linarith
    have h4 : s j * Real.sqrt κh ≤ Real.sqrt (e j) :=
      (pow_le_pow_iff_left₀ (mul_nonneg (hs_nonneg j) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _) two_ne_zero).1 h3
    exact (le_div_iff₀ (Real.sqrt_pos.2 hκh_pos)).2 h4
  have hs_step : ∀ k ≥ N₀ + 1, s k ≤ 1 / 4 * s (k - 1) + 1 / 4 * s (k - 2) +
      (M / κh) * (phiLoj CL θ (e k) - phiLoj CL θ (e (k + 1))) := by
    intro k hk
    by_cases hez : e k = 0
    · have hez1 : e (k + 1) = 0 := le_antisymm (hez ▸ he_anti (Nat.le_succ k)) (he_nonneg _)
      have hsk : s k = 0 := by
        have h1 := hs_sq_le k (by omega)
        rw [hez, hez1, sub_self] at h1
        have h2 : s k ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right h1 hκh_pos
        exact sq_eq_zero_iff.1 (le_antisymm h2 (sq_nonneg _))
      rw [hsk, hez, hez1, sub_self, mul_zero, add_zero]
      linarith [hs_nonneg (k - 1), hs_nonneg (k - 2)]
    · have hepos : 0 < e k := lt_of_le_of_ne (he_nonneg k) (Ne.symm hez)
      have hlj := hLoj_at k hk hez
      have hsum_s : ‖x k - x (k - 1)‖ + ‖y k - y (k - 1)‖ + ‖y (k - 1) - y (k - 2)‖ ≤
          s (k - 1) + s (k - 2) := by
        have hk1 : k - 1 + 1 = k := by omega
        have hk2 : k - 2 + 1 = k - 1 := by omega
        simp only [hsdef, hk1, hk2]
        linarith [norm_nonneg (x (k - 1) - x (k - 2))]
      have hlj' : e k ^ θ ≤ CL * M * (s (k - 1) + s (k - 2)) :=
        hlj.trans (mul_le_mul_of_nonneg_left hsum_s (by positivity))
      have h1 : 1 ≤ CL * e k ^ (-θ) * (M * (s (k - 1) + s (k - 2))) := by
        have hp : 0 < e k ^ θ := Real.rpow_pos_of_pos hepos θ
        rw [Real.rpow_neg hepos.le]
        have h2 := mul_le_mul_of_nonneg_left hlj' (inv_nonneg.2 hp.le)
        rw [inv_mul_cancel₀ hp.ne'] at h2
        calc (1 : ℝ) ≤ (e k ^ θ)⁻¹ * (CL * M * (s (k - 1) + s (k - 2))) := h2
          _ = CL * (e k ^ θ)⁻¹ * (M * (s (k - 1) + s (k - 2))) := by ring
      have hdesc := hs_sq_le k (by omega)
      have hdiff_nonneg : 0 ≤ e k - e (k + 1) := by linarith [he_anti (Nat.le_succ k)]
      have hconc := phiLoj_concave_diff hCL hθ0 hθ1 (he_nonneg (k + 1)) (he_anti (Nat.le_succ k)) hepos
      have hsq_bound : s k ^ 2 ≤ (M / κh) * (phiLoj CL θ (e k) - phiLoj CL θ (e (k + 1))) *
          (s (k - 1) + s (k - 2)) := by
        have hstep1 : κh * s k ^ 2 ≤
            (e k - e (k + 1)) * (CL * e k ^ (-θ) * (M * (s (k - 1) + s (k - 2)))) :=
          hdesc.trans (le_mul_of_one_le_right hdiff_nonneg h1)
        have hstep2 : (e k - e (k + 1)) * (CL * e k ^ (-θ) * (M * (s (k - 1) + s (k - 2)))) =
            (CL * e k ^ (-θ) * (e k - e (k + 1))) * (M * (s (k - 1) + s (k - 2))) := by ring
        rw [hstep2] at hstep1
        have hstep3 : (CL * e k ^ (-θ) * (e k - e (k + 1))) * (M * (s (k - 1) + s (k - 2))) ≤
            (phiLoj CL θ (e k) - phiLoj CL θ (e (k + 1))) * (M * (s (k - 1) + s (k - 2))) :=
          mul_le_mul_of_nonneg_right hconc (mul_nonneg hM.le (add_nonneg (hs_nonneg _) (hs_nonneg _)))
        have hmul := mul_le_mul_of_nonneg_left (hstep1.trans hstep3) (inv_nonneg.2 hκh_pos.le)
        have eL : κh⁻¹ * (κh * s k ^ 2) = s k ^ 2 := by field_simp
        have eR : κh⁻¹ * ((phiLoj CL θ (e k) - phiLoj CL θ (e (k + 1))) * (M * (s (k - 1) + s (k - 2)))) =
            (M / κh) * (phiLoj CL θ (e k) - phiLoj CL θ (e (k + 1))) * (s (k - 1) + s (k - 2)) := by
          field_simp
        linarith
      set Aterm := (M / κh) * (phiLoj CL θ (e k) - phiLoj CL θ (e (k + 1)))
      set Bterm := s (k - 1) + s (k - 2)
      have hA0 : 0 ≤ Aterm := mul_nonneg (by positivity)
        (by linarith [phiLoj_mono hCL hθ1 (he_nonneg (k + 1)) (he_anti (Nat.le_succ k))])
      have hB0 : 0 ≤ Bterm := add_nonneg (hs_nonneg _) (hs_nonneg _)
      have h4 : 4 * (1 / 4 * Bterm) * Aterm ≤ (1 / 4 * Bterm + Aterm) ^ 2 := by
        nlinarith [sq_nonneg (1 / 4 * Bterm - Aterm)]
      have hsq2 : s k ^ 2 ≤ (1 / 4 * Bterm + Aterm) ^ 2 := by linarith
      have hfin := (pow_le_pow_iff_left₀ (hs_nonneg k) (by positivity) two_ne_zero).1 hsq2
      linarith
  set cB : ℝ := 3 / (2 * Real.sqrt κh) + 2 * M / κh with hcBdef
  refine ⟨cB, by positivity, fun k hk => ?_⟩
  set m0 : ℕ := k - 2 with hm0def
  have hm0_ge1 : 1 ≤ m0 := by omega
  have htele : ∀ N : ℕ, ∑ i ∈ Finset.range N, s (k + i) ≤
      cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) := by
    intro N
    have h1 := tele_sum_step s (fun j => phiLoj CL θ (e j)) (M / κh) m0 hs_nonneg
      (fun j => phiLoj_nonneg hCL hθ1 (he_nonneg j)) (by positivity)
      (fun i => by
        have := hs_step (m0 + i + 2) (by omega)
        have e1 : m0 + i + 2 - 1 = m0 + i + 1 := by omega
        have e2 : m0 + i + 2 - 2 = m0 + i := by omega
        have e3 : m0 + i + 2 + 1 = m0 + i + 3 := by omega
        rw [e1, e2, e3] at this
        exact this) N
    have heq_sum : ∑ i ∈ Finset.range N, s (k + i) = ∑ i ∈ Finset.range N, s (m0 + i + 2) := by
      apply Finset.sum_congr rfl; intro i _; congr 1; omega
    rw [heq_sum]
    have hs1 : s (m0 + 1) ≤ Real.sqrt (e m0) / Real.sqrt κh :=
      (hs_le_sqrt (m0 + 1) (by omega)).trans
        (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (he_anti (Nat.le_succ m0))) (Real.sqrt_nonneg _))
    have hs0 : s m0 ≤ Real.sqrt (e m0) / Real.sqrt κh := hs_le_sqrt m0 hm0_ge1
    have hphi : phiLoj CL θ (e (m0 + 2)) ≤ phiLoj CL θ (e m0) :=
      phiLoj_mono hCL hθ1 (he_nonneg (m0 + 2)) (he_anti (by omega))
    have hsq_le : Real.sqrt (e m0) ≤ max (Real.sqrt (e m0)) (phiLoj CL θ (e m0)) := le_max_left _ _
    have hph_le : phiLoj CL θ (e m0) ≤ max (Real.sqrt (e m0)) (phiLoj CL θ (e m0)) := le_max_right _ _
    have h32 : 3 / (2 * Real.sqrt κh) * Real.sqrt (e m0) =
        Real.sqrt (e m0) / Real.sqrt κh + 1 / 2 * (Real.sqrt (e m0) / Real.sqrt κh) := by ring
    have h2m : 2 * (M / κh) * phiLoj CL θ (e (m0 + 2)) ≤
        2 * M / κh * max (Real.sqrt (e m0)) (phiLoj CL θ (e m0)) := by
      have : 2 * (M / κh) * phiLoj CL θ (e (m0 + 2)) = 2 * M / κh * phiLoj CL θ (e (m0 + 2)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (hphi.trans hph_le) (by positivity)
    have hsqrt_bound : 3 / (2 * Real.sqrt κh) * Real.sqrt (e m0) ≤
        3 / (2 * Real.sqrt κh) * max (Real.sqrt (e m0)) (phiLoj CL θ (e m0)) :=
      mul_le_mul_of_nonneg_left hsq_le (by positivity)
    rw [hcBdef, add_mul]
    linarith
  have hxk : ‖x k - xh‖ ≤ cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) := by
    refine norm_sub_limit_le x xh hxh k _ (fun N => ?_)
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (htele N)
    simp only [hsdef]; linarith [norm_nonneg (y (k + i + 1) - y (k + i))]
  have hyk : ‖y k - yh‖ ≤ cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) := by
    refine norm_sub_limit_le y yh hyh k _ (fun N => ?_)
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (htele N)
    simp only [hsdef]; linarith [norm_nonneg (x (k + i + 1) - x (k + i))]
  have hzk : ‖z k - zh‖ ≤ (‖A‖ + 1 / (ρ * r)) *
      (cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2)))) := by
    have ez : z k - zh = A (x k - xh) - (A (x k) - z k) := by
      rw [hzh_eq, map_sub]; abel
    rw [ez]
    have hresk := hres (k - 1)
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1] at hresk
    have hyn : ‖y k - y (k - 1)‖ ≤ cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) := by
      have hs1 : ‖y k - y (k - 1)‖ ≤ s (k - 1) := by
        simp only [hsdef, hk1]; linarith [norm_nonneg (x k - x (k - 1))]
      have hs2 : s (k - 1) ≤ Real.sqrt (e (k - 2)) / Real.sqrt κh :=
        (hs_le_sqrt (k - 1) (by omega)).trans
          (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (he_anti (by omega))) (Real.sqrt_nonneg _))
      have hle1 : Real.sqrt (e (k - 2)) / Real.sqrt κh ≤
          3 / (2 * Real.sqrt κh) * Real.sqrt (e (k - 2)) := by
        have hnn : 0 ≤ Real.sqrt (e (k - 2)) / Real.sqrt κh := by positivity
        have heq : 3 / (2 * Real.sqrt κh) * Real.sqrt (e (k - 2)) =
            (3 / 2) * (Real.sqrt (e (k - 2)) / Real.sqrt κh) := by ring
        linarith
      have hle2 : 3 / (2 * Real.sqrt κh) * Real.sqrt (e (k - 2)) ≤
          cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) := by
        have h1 : Real.sqrt (e (k - 2)) ≤ max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) :=
          le_max_left _ _
        have h2 : 0 ≤ max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) :=
          le_trans (Real.sqrt_nonneg _) h1
        have h3 : 3 / (2 * Real.sqrt κh) ≤ cB := by
          rw [hcBdef]; linarith [show 0 ≤ 2 * M / κh by positivity]
        calc 3 / (2 * Real.sqrt κh) * Real.sqrt (e (k - 2))
            ≤ 3 / (2 * Real.sqrt κh) * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) :=
              mul_le_mul_of_nonneg_right h3 h2
      linarith
    have hA_le := A.le_opNorm (x k - xh)
    have htri := norm_sub_le (A (x k - xh)) (A (x k) - z k)
    have hdiv_le : ‖y k - y (k - 1)‖ / (ρ * r) ≤
        1 / (ρ * r) * (cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2)))) := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hyn hρr.le
    have hA_mul : ‖A‖ * ‖x k - xh‖ ≤
        ‖A‖ * (cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2)))) :=
      mul_le_mul_of_nonneg_left hxk (norm_nonneg A)
    linarith
  exact ⟨hxk, hyk, hzk⟩

lemma assemble_three_rates {n m : ℕ} (x : ℕ → E n) (z y : ℕ → E m) (xh : E n) (zh yh : E m)
    (e : ℕ → ℝ) (cB cZ CL θ : ℝ) (N₂ : ℕ)
    (hcB : 0 < cB) (hcZ : 0 < cZ) (hCL : 0 < CL) (hθ1 : θ < 1) (hN₂ : 3 ≤ N₂)
    (h15 : (θ = 0 → ∃ K : ℕ, ∀ k ≥ K, e k = 0) ∧
      (0 < θ ∧ θ ≤ 1 / 2 → ∃ Ce0 : ℝ, 0 < Ce0 ∧ ∃ Q : ℝ, 0 ≤ Q ∧ Q < 1 ∧
        ∀ k ≥ N₂, 0 ≤ e k ∧ e k ≤ Ce0 * Q ^ k) ∧
      (1 / 2 < θ ∧ θ < 1 → ∃ Ce1 : ℝ, 0 < Ce1 ∧
        ∀ k ≥ N₂ + 2, 0 ≤ e k ∧ e k ≤ Ce1 * ((k : ℝ) - (2 : ℕ) + 1) ^ (-(1 / (2 * θ - 1)))))
    (hiter : ∀ k ≥ N₂,
      ‖x k - xh‖ ≤ cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) ∧
      ‖y k - yh‖ ≤ cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) ∧
      ‖z k - zh‖ ≤ cZ * (cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))))) :
    (θ = 0 → ∃ K : ℕ, ∀ k ≥ K, x k = xh ∧ z k = zh ∧ y k = yh) ∧
    (0 < θ ∧ θ ≤ 1 / 2 → ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      ∃ C01 C02 C03 Qhat : ℝ, 0 < C01 ∧ 0 < C02 ∧ 0 < C03 ∧ 0 ≤ Qhat ∧ Qhat < 1 ∧
      ∀ k ≥ k₀, ‖x k - xh‖ ≤ C01 * Qhat ^ k ∧ ‖y k - yh‖ ≤ C02 * Qhat ^ k ∧
        ‖z k - zh‖ ≤ C03 * Qhat ^ k) ∧
    (1 / 2 < θ ∧ θ < 1 → ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∃ C11 C12 C13 : ℝ, 0 < C11 ∧ 0 < C12 ∧ 0 < C13 ∧
      ∀ k ≥ k₀, ‖x k - xh‖ ≤ C11 * ((k : ℝ) - 1) ^ (-((1 - θ) / (2 * θ - 1))) ∧
        ‖y k - yh‖ ≤ C12 * ((k : ℝ) - 1) ^ (-((1 - θ) / (2 * θ - 1))) ∧
        ‖z k - zh‖ ≤ C13 * ((k : ℝ) - 2) ^ (-((1 - θ) / (2 * θ - 1)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hθ
    obtain ⟨K₁, hK₁⟩ := h15.1 hθ
    refine ⟨max K₁ N₂ + 2, fun k hk => ?_⟩
    obtain ⟨hxk, hyk, hzk⟩ := hiter k (by omega)
    have he0 : e (k - 2) = 0 := hK₁ (k - 2) (by omega)
    have hM0 : max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) = 0 := by
      rw [he0, hθ]; simp [phiLoj]
    rw [hM0, mul_zero] at hxk hyk hzk
    rw [mul_zero] at hzk
    exact ⟨sub_eq_zero.1 (norm_le_zero_iff.1 hxk),
           sub_eq_zero.1 (norm_le_zero_iff.1 hzk),
           sub_eq_zero.1 (norm_le_zero_iff.1 hyk)⟩
  · rintro ⟨hθp, hθh⟩
    obtain ⟨Ce0, hCe0, Q, hQ0, hQ1, hb⟩ := h15.2.1 ⟨hθp, hθh⟩
    set Q' : ℝ := max Q (1 / 2)
    have hQ'0 : 0 < Q' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hQ'1 : Q' < 1 := max_lt hQ1 (by norm_num)
    set Qhat : ℝ := Real.sqrt Q'
    have hQh0 : 0 < Qhat := Real.sqrt_pos.2 hQ'0
    have hQh1 : Qhat < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hQ'1
    set D : ℝ := max (Real.sqrt Ce0) (CL * Ce0 ^ (1 - θ) / (1 - θ))
    have hD_pos : 0 < D := lt_of_lt_of_le (Real.sqrt_pos.2 hCe0) (le_max_left _ _)
    refine ⟨N₂ + 2, by omega,
      cB * D / Qhat ^ 2, cB * D / Qhat ^ 2, cZ * (cB * D / Qhat ^ 2), Qhat,
      by positivity, by positivity, by positivity, hQh0.le, hQh1, fun k hk => ?_⟩
    obtain ⟨hxk, hyk, hzk⟩ := hiter k (by omega)
    obtain ⟨he1, he2⟩ := hb (k - 2) (by omega)
    have he2' : e (k - 2) ≤ Ce0 * Q' ^ (k - 2) :=
      he2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 (le_max_left _ _) _) hCe0.le)
    obtain ⟨a1, a2⟩ := lin_aux Q' θ (k - 2) hQ'0 hQ'1.le hθh
    have hM := key_max_bound CL θ Ce0 (e (k - 2)) (Q' ^ (k - 2)) (Qhat ^ (k - 2))
      hCL hθ1 hCe0 he1 he2' (pow_nonneg hQ'0.le _) a1 a2
    have hpow : Qhat ^ (k - 2) = Qhat ^ k / Qhat ^ 2 := by
      have : k = (k - 2) + 2 := by omega
      conv_rhs => rw [this, pow_add]
      field_simp
    have hB_le : cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) ≤
        cB * D / Qhat ^ 2 * Qhat ^ k := by
      calc cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2)))
          ≤ cB * (D * Qhat ^ (k - 2)) := mul_le_mul_of_nonneg_left hM hcB.le
        _ = cB * D / Qhat ^ 2 * Qhat ^ k := by rw [hpow]; ring
    exact ⟨hxk.trans hB_le, hyk.trans hB_le,
      hzk.trans (by
        calc cZ * (cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))))
            ≤ cZ * (cB * D / Qhat ^ 2 * Qhat ^ k) := mul_le_mul_of_nonneg_left hB_le hcZ.le
          _ = cZ * (cB * D / Qhat ^ 2) * Qhat ^ k := by ring)⟩
  · rintro ⟨hθa, hθb⟩
    obtain ⟨Ce1, hCe1, hb⟩ := h15.2.2 ⟨hθa, hθb⟩
    set D : ℝ := max (Real.sqrt Ce1) (CL * Ce1 ^ (1 - θ) / (1 - θ))
    have hD_pos : 0 < D := lt_of_lt_of_le (Real.sqrt_pos.2 hCe1) (le_max_left _ _)
    set q : ℝ := (1 - θ) / (2 * θ - 1)
    have hq_pos : 0 < q := div_pos (by linarith) (by linarith)
    refine ⟨max (N₂ + 4) 6, by omega,
      cB * D * 2 ^ q, cB * D * 2 ^ q, cZ * (cB * D * 2 ^ q),
      by positivity, by positivity, by positivity, fun k hk => ?_⟩
    obtain ⟨hxk, hyk, hzk⟩ := hiter k (by omega)
    obtain ⟨he1, he2⟩ := hb (k - 2) (by omega)
    have hcast : ((k - 2 : ℕ) : ℝ) - (2 : ℕ) + 1 = (k : ℝ) - 3 := by
      have : 2 ≤ k := by omega
      push_cast [Nat.cast_sub this]; ring
    rw [hcast] at he2
    have hk6 : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_trans (le_max_right _ _) hk)
    have ht1 : (1 : ℝ) ≤ (k : ℝ) - 3 := by linarith
    obtain ⟨a1, a2⟩ := sub_aux ((k : ℝ) - 3) θ ht1 hθa hθb
    have hM := key_max_bound CL θ Ce1 (e (k - 2)) (((k : ℝ) - 3) ^ (-(1 / (2 * θ - 1))))
      (((k : ℝ) - 3) ^ (-q)) hCL hθ1 hCe1 he1 he2 (Real.rpow_nonneg (by linarith) _) a1 a2
    have hshift : ((k : ℝ) - 3) ^ (-q) ≤ 2 ^ q * ((k : ℝ) - 1) ^ (-q) :=
      rpow_neg_shift ((k : ℝ) - 3) ((k : ℝ) - 1) q (by linarith) (by linarith) hq_pos (by linarith)
    have hB_le : cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2))) ≤
        cB * D * 2 ^ q * ((k : ℝ) - 1) ^ (-q) := by
      calc cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2)))
          ≤ cB * (D * ((k : ℝ) - 3) ^ (-q)) := mul_le_mul_of_nonneg_left hM hcB.le
        _ ≤ cB * (D * (2 ^ q * ((k : ℝ) - 1) ^ (-q))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hshift hD_pos.le) hcB.le
        _ = cB * D * 2 ^ q * ((k : ℝ) - 1) ^ (-q) := by ring
    have hz_shift : ((k : ℝ) - 1) ^ (-q) ≤ ((k : ℝ) - 2) ^ (-q) := by
      rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) q)
        (Real.rpow_le_rpow (by linarith) (by linarith) hq_pos.le)
    refine ⟨hxk.trans hB_le, hyk.trans hB_le, ?_⟩
    calc ‖z k - zh‖ ≤ cZ * (cB * max (Real.sqrt (e (k - 2))) (phiLoj CL θ (e (k - 2)))) := hzk
      _ ≤ cZ * (cB * D * 2 ^ q * ((k : ℝ) - 1) ^ (-q)) := mul_le_mul_of_nonneg_left hB_le hcZ.le
      _ ≤ cZ * (cB * D * 2 ^ q * ((k : ℝ) - 2) ^ (-q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz_shift (by positivity)) hcZ.le
      _ = cZ * (cB * D * 2 ^ q) * ((k : ℝ) - 2) ^ (-q) := by ring

end BotNguyenADMM.Rates.ProxMu1ZeroAux

open BotNguyenADMM.Rates BotNguyenADMM.Rates.ProxMu1ZeroAux in
theorem solution
    {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (g : BotNguyenADMM.KL.E m → EReal) (h : BotNguyenADMM.KL.E n → ℝ) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m)
    (L r ρ lam μ₁ μ₂ : ℝ) (M₁ : ℕ → BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E n) (M₂ : ℕ → BotNguyenADMM.KL.E m →L[ℝ] BotNguyenADMM.KL.E m)
    (hv : v = BotNguyenADMM.KL.Variant.prox) (hμ₁ : μ₁ = 0)
    (hA2 : Assumption2 v g h A L r ρ lam μ₁ μ₂ M₁ M₂)
    (x : ℕ → BotNguyenADMM.KL.E n) (z y : ℕ → BotNguyenADMM.KL.E m) (hrun : IsRun v g h A r ρ M₁ M₂ x z y)
    (hbx : Bornology.IsBounded (Set.range x)) (hbz : Bornology.IsBounded (Set.range z))
    (hby : Bornology.IsBounded (Set.range y))
    (xh : BotNguyenADMM.KL.E n) (zh yh : BotNguyenADMM.KL.E m) (CL θ : ℝ)
    (hloj : LojAt v g h A L r ρ lam μ₁ x z y xh zh yh CL θ) :
    (θ = 0 → ∃ K : ℕ, ∀ k ≥ K, x k = xh ∧ z k = zh ∧ y k = yh) ∧
    (0 < θ ∧ θ ≤ 1 / 2 → ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      ∃ C01 C02 C03 Qhat : ℝ, 0 < C01 ∧ 0 < C02 ∧ 0 < C03 ∧ 0 ≤ Qhat ∧ Qhat < 1 ∧
      ∀ k ≥ k₀, ‖x k - xh‖ ≤ C01 * Qhat ^ k ∧ ‖y k - yh‖ ≤ C02 * Qhat ^ k ∧
        ‖z k - zh‖ ≤ C03 * Qhat ^ k) ∧
    (1 / 2 < θ ∧ θ < 1 → ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∃ C11 C12 C13 : ℝ, 0 < C11 ∧ 0 < C12 ∧ 0 < C13 ∧
      ∀ k ≥ k₀, ‖x k - xh‖ ≤ C11 * ((k : ℝ) - 1) ^ (-((1 - θ) / (2 * θ - 1))) ∧
        ‖y k - yh‖ ≤ C12 * ((k : ℝ) - 1) ^ (-((1 - θ) / (2 * θ - 1))) ∧
        ‖z k - zh‖ ≤ C13 * ((k : ℝ) - 2) ^ (-((1 - θ) / (2 * θ - 1)))) := by
  subst hv; subst hμ₁
  obtain ⟨hCL, hθ0, hθ1, hxh, hzh, hyh, ε, hε, hLoj⟩ := hloj
  have hT0 := T0_pos hA2.lam_pos hA2.ρ_pos hA2.ρ_lt_two
  have hL := L_pos_of_A2 hA2
  have hr := hA2.r_pos
  have hρ := hA2.ρ_pos
  have hρr : 0 < ρ * r := mul_pos hρ hr
  obtain ⟨Rx, hRx⟩ := hbx.exists_norm_le
  obtain ⟨Rz, hRz⟩ := hbz.exists_norm_le
  obtain ⟨Ry, hRy⟩ := hby.exists_norm_le
  set R : ℝ := max Rx (max Rz Ry)
  have hR : ∀ k, ‖x k‖ ≤ R ∧ ‖z k‖ ≤ R ∧ ‖y k‖ ≤ R := fun k =>
    ⟨(hRx _ ⟨k, rfl⟩).trans (le_max_left _ _),
     (hRz _ ⟨k, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _)),
     (hRy _ ⟨k, rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  obtain ⟨gs, hgs, hgt⟩ := g_lim_limit hA2 hrun R hR zh hzh
  have hFstar_eq : Fstar .prox g h A L r ρ lam 0 xh zh yh =
      ((gs + R3 h A r xh zh yh : ℝ) : EReal) := by
    unfold Fstar
    rw [Freg_pack5_zero, hgs, ← EReal.coe_add]
    simp
  have hFstar_toReal : (Fstar .prox g h A L r ρ lam 0 xh zh yh).toReal = gs + R3 h A r xh zh yh := by
    rw [hFstar_eq, EReal.toReal_coe]
  set E := Ek .prox g h A L r ρ lam 0 x z y xh zh yh with hEdef
  set e : ℕ → ℝ := fun k => if k = 0 then E 1 else E k with hedef
  have he_eq : ∀ k, 1 ≤ k → e k = E k := fun k hk => by simp [hedef, Nat.ne_of_gt hk]
  have hE_succ : ∀ k, E (k + 1) = FR g h A r ρ lam x z y k - (gs + R3 h A r xh zh yh) := by
    intro k
    simp only [hEdef, Ek, Fk_succ_eq hA2 hrun k, EReal.toReal_coe, hFstar_toReal]
  set κ : ℝ := min (2 * T0 lam ρ * L ^ 2 / r) (1 / (ρ * r)) with hκdef
  have hκ_pos : 0 < κ := lt_min (by positivity) (by positivity)
  have he_desc : ∀ k ≥ 1, e (k + 1) + κ * (‖x (k + 1) - x k‖ ^ 2 + ‖y (k + 1) - y k‖ ^ 2) ≤ e k := by
    intro k hk
    rw [he_eq (k + 1) (by omega), he_eq k hk]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hE_succ (j + 1), hE_succ j]
    have hd := FR_descent hA2 hrun j
    have hc1 : κ * ‖x (j + 2) - x (j + 1)‖ ^ 2 ≤
        (2 * T0 lam ρ * L ^ 2 / r) * ‖x (j + 2) - x (j + 1)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    have hc2 : κ * ‖y (j + 2) - y (j + 1)‖ ^ 2 ≤
        (1 / (ρ * r)) * ‖y (j + 2) - y (j + 1)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    simp only [show j + 1 + 1 = j + 2 from rfl] at hd hc1 hc2 ⊢
    linarith
  have he_anti : Antitone e := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    cases k with
    | zero => simp [hedef]
    | succ j =>
      have := he_desc (j + 1) (by omega)
      have h0 : 0 ≤ κ * (‖x (j + 2) - x (j + 1)‖ ^ 2 + ‖y (j + 2) - y (j + 1)‖ ^ 2) := by positivity
      linarith
  have hx1 : Tendsto (fun k => x (k + 1)) atTop (𝓝 xh) := hxh.comp (tendsto_add_atTop_nat 1)
  have hz1 : Tendsto (fun k => z (k + 1)) atTop (𝓝 zh) := hzh.comp (tendsto_add_atTop_nat 1)
  have hy1 : Tendsto (fun k => y (k + 1)) atTop (𝓝 yh) := hyh.comp (tendsto_add_atTop_nat 1)
  have hFR_lim : Tendsto (FR g h A r ρ lam x z y) atTop (𝓝 (gs + R3 h A r xh zh yh)) := by
    have hAx : Tendsto (fun k => A (x (k + 1)) - z (k + 1)) atTop (𝓝 (A xh - zh)) :=
      ((A.continuous.tendsto _).comp hx1).sub hz1
    have hR3 : Tendsto (fun k => R3 h A r (x (k + 1)) (z (k + 1)) (y (k + 1))) atTop
        (𝓝 (R3 h A r xh zh yh)) :=
      (((hA2.h_diff.continuous.tendsto _).comp hx1).add (hy1.inner hAx)).add
        ((hAx.norm.pow 2).const_mul _)
    have hT : Tendsto (fun k => 2 * T1 lam ρ r * ‖(ContinuousLinearMap.adjoint A) (y (k + 1) - y k)‖ ^ 2)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => (ContinuousLinearMap.adjoint A) (y (k + 1) - y k)) atTop
          (𝓝 ((ContinuousLinearMap.adjoint A) (yh - yh))) :=
        ((ContinuousLinearMap.adjoint A).continuous.tendsto _).comp (hy1.sub hyh)
      rw [sub_self, map_zero] at h1
      simpa using ((h1.norm.pow 2).const_mul (2 * T1 lam ρ r))
    have hall := (hgt.add hR3).add hT
    rw [add_zero] at hall
    exact hall
  have he_lim : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => E (k + 1)) atTop (𝓝 0) := by
      have := hFR_lim.sub_const (gs + R3 h A r xh zh yh)
      rw [sub_self] at this
      exact this.congr (fun k => (hE_succ k).symm)
    have h2 : Tendsto (fun k => e (k + 1)) atTop (𝓝 0) :=
      h1.congr (fun k => (he_eq (k + 1) (by omega)).symm)
    exact (tendsto_add_atTop_iff_nat 1).1 h2
  have he_nonneg : ∀ k, 0 ≤ e k := fun k => he_anti.le_of_tendsto he_lim k
  have hzh_eq : zh = A xh := by
    have h1 : Tendsto (fun k => A (x (k + 1)) - z (k + 1)) atTop (𝓝 (A xh - zh)) :=
      ((A.continuous.tendsto _).comp hx1).sub hz1
    have h2 : Tendsto (fun k => A (x (k + 1)) - z (k + 1)) atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
      have hy0 : Tendsto (fun k => ‖y (k + 1) - y k‖ / (ρ * r)) atTop (𝓝 0) := by
        have := ((hy1.sub hyh).norm).div_const (ρ * r)
        simpa [sub_self] using this
      exact hy0.congr (fun k => (res_norm hρ hr hrun k).symm)
    exact (sub_eq_zero.1 (tendsto_nhds_unique h1 h2)).symm
  obtain ⟨M, hM_pos, hV_bound⟩ := V_norm_bound hA2 hrun
  have hW_lim : Tendsto (Wpt x z y) atTop (𝓝 (pack5 xh zh yh xh yh)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsum0 : Tendsto (fun k => ‖x (k + 1) - xh‖ + ‖z (k + 1) - zh‖ + ‖y (k + 1) - yh‖ +
        ‖x k - xh‖ + ‖y k - yh‖) atTop (𝓝 0) := by
      have := (((((tendsto_iff_norm_sub_tendsto_zero.1 hx1).add
        (tendsto_iff_norm_sub_tendsto_zero.1 hz1)).add
        (tendsto_iff_norm_sub_tendsto_zero.1 hy1)).add
        (tendsto_iff_norm_sub_tendsto_zero.1 hxh)).add
        (tendsto_iff_norm_sub_tendsto_zero.1 hyh))
      simpa using this
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hsum0
    unfold Wpt
    rw [pack5_sub]
    exact norm_pack5_le _ _ _ _ _
  obtain ⟨N₀', hN₀'⟩ := (hW_lim.eventually (Metric.ball_mem_nhds _ hε)).exists_forall_of_atTop
  set N₀ : ℕ := max N₀' 2 with hN₀def
  have hLoj_at : ∀ k ≥ N₀ + 1, e k ≠ 0 →
      e k ^ θ ≤ CL * M * (‖x k - x (k - 1)‖ + ‖y k - y (k - 1)‖ + ‖y (k - 1) - y (k - 2)‖) := by
    intro k hk hene
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : N₀' ≤ j := by omega
    have hj1 : 1 ≤ j := by omega
    have hFW : Freg .prox g h A L r ρ lam 0 (Wpt x z y j) = (FR g h A r ρ lam x z y j : EReal) :=
      Fk_succ_eq hA2 hrun j
    have he_val : e (j + 1) = (Freg .prox g h A L r ρ lam 0 (Wpt x z y j)).toReal -
        (Fstar .prox g h A L r ρ lam 0 xh zh yh).toReal := by
      rw [he_eq (j + 1) (by omega), hE_succ j, hFW, EReal.toReal_coe, hFstar_toReal]
    have hneF : Freg .prox g h A L r ρ lam 0 (Wpt x z y j) ≠
        Fstar .prox g h A L r ρ lam 0 xh zh yh := by
      intro heq; apply hene; rw [he_val, heq, sub_self]
    have hlj := hLoj (Wpt x z y j) (hN₀' j hj) (Vsub h A r ρ lam M₂ x z y j) (V_lim hA2 hrun j) hneF
    rw [← he_val, abs_of_nonneg (he_nonneg (j + 1))] at hlj
    have hsub1 : j + 1 - 1 = j := by omega
    have hsub2 : j + 1 - 2 = j - 1 := by omega
    rw [hsub1, hsub2]
    calc e (j + 1) ^ θ ≤ CL * ‖Vsub h A r ρ lam M₂ x z y j‖ := hlj
      _ ≤ CL * (M * (‖x (j + 1) - x j‖ + ‖y (j + 1) - y j‖ + ‖y j - y (j - 1)‖)) :=
        mul_le_mul_of_nonneg_left (hV_bound j hj1) hCL.le
      _ = CL * M * (‖x (j + 1) - x j‖ + ‖y (j + 1) - y j‖ + ‖y j - y (j - 1)‖) := by ring
  have hrec15 := rec_for_lemma15 x y e κ CL M θ N₀ (by omega) hκ_pos hCL hM_pos he_nonneg he_anti
    he_desc hLoj_at
  have h15 := BotNguyenADMM.Rates.lemma_15 e he_nonneg he_anti he_lim (N₀ + 1) 2 (by omega) (by omega)
    (κ / (3 * CL ^ 2 * M ^ 2)) θ (by positivity) hθ0 hθ1 hrec15
  obtain ⟨cB, hcB_pos, hiter⟩ := iter_tail_bounds A ρ r hρr x z y xh zh yh hxh hyh hzh_eq
    (res_norm hρ hr hrun) e κ CL M θ N₀ (by omega) hκ_pos hCL hM_pos hθ0 hθ1
    he_nonneg he_anti he_desc hLoj_at
  exact assemble_three_rates x z y xh zh yh e cB (‖A‖ + 1 / (ρ * r)) CL θ (N₀ + 1)
    hcB_pos (by positivity) hCL hθ1 (by omega) h15 hiter
