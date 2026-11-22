-- Prove2me | solution 1 for FluxFieldBootstrapRound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:27:17.070145+00:00
-- url     : https://prove2.me/submissions/024fb111-d155-44b1-b6ba-008e6bf070ac

import Definitions.Def_PHigherOrder_BootstrapRound
import Definitions.Def_PHigherOrder_CoeffFieldFromScalarBounds
import Definitions.Def_PHigherOrder_FluxJacobianElliptic
import Definitions.Def_PHigherOrder_GradientAnnulus
import Definitions.Def_PHigherOrder_FluxFieldBootstrapRound
import Theorems.Thm_BootstrapRound
import Theorems.Thm_CoeffFieldFromScalarBounds
import Theorems.Thm_FluxJacobianElliptic
import Theorems.Thm_GradientAnnulus


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p) (hS : DivFormSchauderInput)
    (κ : ℝ) (hκdef : κ = F.kappa) (i : ℕ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (r r' : ℝ) (hr' : 0 < r') (hrr : r' < r) (D : ℝ) (hD : 0 < D) :
    ∃ D' : ℝ, 0 < D' ∧ 1 ≤ D' ∧
      ∀ (v : Plane → ℝ) (V : Set Plane),
      IsOpen V → Convex ℝ V → (∀ ζ ∈ V, a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) →
      (∀ x ∈ Metric.ball (0 : Plane) r, gradient v x ∈ V) →
      ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) →
      (∀ x ∈ Metric.ball (0 : Plane) r, |v x| ≤ 1) →
      (∀ x ∈ Metric.ball (0 : Plane) r, ‖gradient v x‖ ≤ F.C₀) →
      (∀ m ≤ i + 1, ∀ x ∈ Metric.ball (0 : Plane) r,
          ‖iteratedFDeriv ℝ m v x‖ ≤ D) →
      (∀ x ∈ Metric.ball (0 : Plane) r, ∀ y ∈ Metric.ball (0 : Plane) r,
          ‖iteratedFDeriv ℝ (i + 1) v x - iteratedFDeriv ℝ (i + 1) v y‖
            ≤ D * ‖x - y‖ ^ κ) →
      (∀ e : Plane, IsLinearDivSol (Metric.ball 0 r)
          (fun x => FluxJacobian p (gradient v x))
          (fun x => inner ℝ (gradient v x) e)
          (fun x => gradient (fun y => inner ℝ (gradient v y) e) x)) →
      (∀ m ≤ i + 2, ∀ x ∈ Metric.ball (0 : Plane) r',
          ‖iteratedFDeriv ℝ m v x‖ ≤ D')
        ∧ (∀ x ∈ Metric.ball (0 : Plane) r',
            ∀ y ∈ Metric.ball (0 : Plane) r',
            ‖iteratedFDeriv ℝ (i + 2) v x - iteratedFDeriv ℝ (i + 2) v y‖
              ≤ D' * ‖x - y‖ ^ κ) := by
  have hκ0 : 0 < κ := by rw [hκdef]; exact F.kappa_pos
  have hκ1 : κ < 1 := by rw [hκdef]; exact F.kappa_lt_one
  have hC0 : 0 < F.C₀ := F.C₀_pos
  have hr : 0 < r := lt_trans hr' hrr
  -- The flux-Jacobian constants on the annulus, and the ellipticity pair.
  obtain ⟨hFJd, hFJC, hlam0, hlamLam, hFJell, hFJM, hFJAp⟩ :=
    FluxJacobianElliptic p hp hp2 a b ha hab
  obtain ⟨lam, hlamdef⟩ : ∃ t : ℝ, t = (p - 1) * b ^ (p - 2) := ⟨_, rfl⟩
  obtain ⟨Lam, hLamdef⟩ : ∃ t : ℝ, t = a ^ (p - 2) := ⟨_, rfl⟩
  have hlam0' : 0 < lam := by rw [hlamdef]; exact hlam0
  have hlamLam' : lam ≤ Lam := by rw [hlamdef, hLamdef]; exact hlamLam
  -- One bound for the flux Jacobian up to the order this round consumes.
  choose! MΦ hMΦ0 hMΦb using hFJM
  obtain ⟨CΦ, hCΦdef⟩ : ∃ t : ℝ, t = 1 + ∑ j ∈ Finset.range (i + 2), MΦ j := ⟨_, rfl⟩
  have hCΦ0 : 0 < CΦ := by
    rw [hCΦdef]
    have h : 0 ≤ ∑ j ∈ Finset.range (i + 2), MΦ j :=
      Finset.sum_nonneg (fun j _ => le_of_lt (hMΦ0 j))
    linarith
  have hCΦb : ∀ i' ≤ i + 1, ∀ ξ : Plane, a ≤ ‖ξ‖ → ‖ξ‖ ≤ b →
      ‖iteratedFDeriv ℝ i' (FluxJacobian p) ξ‖ ≤ CΦ := by
    intro i' hi' ξ h1 h2
    refine le_trans (hMΦb i' ξ h1 h2) ?_
    rw [hCΦdef]
    have hmem : i' ∈ Finset.range (i + 2) := Finset.mem_range.mpr (by omega)
    have := Finset.single_le_sum (f := MΦ) (fun j _ => le_of_lt (hMΦ0 j)) hmem
    linarith
  -- The diameter of `ball 0 r` is at most `2 r`.
  obtain ⟨d, hddef⟩ : ∃ t : ℝ, t = 2 * r := ⟨_, rfl⟩
  have hd : 0 < d := by rw [hddef]; linarith
  have hball : ∀ x ∈ Metric.ball (0 : Plane) r,
      ∀ y ∈ Metric.ball (0 : Plane) r, ‖x - y‖ ≤ d := by
    intro x hx y hy
    rw [Metric.mem_ball, dist_zero_right] at hx hy
    rw [hddef]
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith
  obtain ⟨M, hM, hCF⟩ :=
    CoeffFieldFromScalarBounds (Plane →L[ℝ] Plane) i κ hκ0 (le_of_lt hκ1) CΦ D d hCΦ0 hD hd
  -- `P_i` from one bootstrap round
  obtain ⟨P, hP, hBR⟩ :=
    BootstrapRound hS i κ hκ0 hκ1 lam Lam hlam0' hlamLam' M F.C₀ hM hC0
      r r' hr' hrr
  refine ⟨1 + max 1 P, by positivity, by simp, ?_⟩
  intro v V hVo hVc hVann hgV hvC hv1 hgb hsup hhol hdiv
  have hVsub : V ⊆ {ζ : Plane | ζ ≠ 0} := by
    intro ζ hζ
    have := (hVann ζ hζ).1
    show ζ ≠ 0
    intro hc
    rw [hc, norm_zero] at this
    linarith
  have hUo : IsOpen (Metric.ball (0 : Plane) r) := Metric.isOpen_ball
  have hUc : Convex ℝ (Metric.ball (0 : Plane) r) := convex_ball 0 r
  -- the gradient field is smooth on the ball
  have hgfac : gradient v
      = (fun T : Plane →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ Plane).symm T) ∘ fderiv ℝ v := by
    funext z
    show gradient v z = (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ v z)
    rw [← toDual_gradient, LinearIsometryEquiv.symm_apply_apply]
  have hgC : ContDiffOn ℝ (⊤ : ℕ∞) (gradient v) (Metric.ball 0 r) := by
    rw [hgfac]
    exact (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp_contDiffOn
      (hvC.fderiv_of_isOpen hUo (by norm_cast))
  -- the coefficient-field bounds, from the coefficient-field node
  obtain ⟨hAsup, hAhol⟩ :=
    hCF (Metric.ball 0 r) V (FluxJacobian p) v hUo hUc hball hVo hVc hgV
      (hFJC.mono hVsub)
      (fun i' hi' ξ hξ => hCΦb i' (by omega) ξ (hVann ξ hξ).1 (hVann ξ hξ).2)
      hvC hsup hhol
  -- the coefficient field is of class `C^i` on the ball
  have hAC : ContDiffOn ℝ (i : ℕ∞) (fun x => FluxJacobian p (gradient v x))
      (Metric.ball 0 r) :=
    ((hFJC.comp hgC (fun x hx => hVsub (hgV x hx))).of_le (by exact_mod_cast le_top))
  -- uniform ellipticity of the coefficient field on the ball
  have hAell : ∀ x ∈ Metric.ball (0 : Plane) r, ∀ ξ : Plane,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ ((fun x => FluxJacobian p (gradient v x)) x ξ) ξ
        ∧ ‖(fun x => FluxJacobian p (gradient v x)) x ξ‖ ≤ Lam * ‖ξ‖ := by
    intro x hx ξ
    obtain ⟨h1, h2⟩ := hVann _ (hgV x hx)
    obtain ⟨e1, e2⟩ := hFJell (gradient v x) h1 h2 ξ
    rw [hlamdef, hLamdef]
    exact ⟨e1, e2⟩
  -- one bootstrap round
  obtain ⟨hvsup, hvhol⟩ :=
    hBR v (fun x => FluxJacobian p (gradient v x)) hvC hgb hAell hAC
      (fun m hm x hx => hAsup m hm x hx) (fun x hx y hy => hAhol x hx y hy) hdiv
  have hPle : P ≤ 1 + max 1 P := by
    have : P ≤ max 1 P := le_max_right 1 P
    linarith
  refine ⟨?_, ?_⟩
  · intro m hm x hx
    rcases Nat.eq_zero_or_pos m with hm0 | hm1
    · subst hm0
      rw [norm_iteratedFDeriv_zero]
      have hxin : x ∈ Metric.ball (0 : Plane) r :=
        Metric.ball_subset_ball (le_of_lt hrr) hx
      have := hv1 x hxin
      have h1 : (1 : ℝ) ≤ max 1 P := le_max_left 1 P
      calc ‖v x‖ = |v x| := Real.norm_eq_abs _
        _ ≤ 1 := this
        _ ≤ 1 + max 1 P := by linarith
    · exact le_trans (hvsup m hm1 hm x hx) hPle
  · intro x hx y hy
    refine le_trans (hvhol x hx y hy) ?_
    have hpow : (0 : ℝ) ≤ ‖x - y‖ ^ κ := Real.rpow_nonneg (norm_nonneg _) κ
    exact mul_le_mul_of_nonneg_right hPle hpow
