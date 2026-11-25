-- Prove2me | solution 1 for DiscreteStability.trap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:03:58.127858+00:00
-- url     : https://prove2.me/submissions/430dcbf3-3ea0-4725-9094-baf73c88c10c

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability
import Theorems.Thm_DiscreteStability_LocalHyp_continuousOn
import Theorems.Thm_DiscreteStability_LocalHyp_grad_xbar_eq_zero
import Theorems.Thm_DiscreteStability_StepBound_hi_nonneg
import Theorems.Thm_DiscreteStability_StepBound_norm_le
import Theorems.Thm_DiscreteStability_exists_pos_lower_bound
import Theorems.Thm_DiscreteStability_step_weighted


set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
variable [FiniteDimensional ℝ E]
namespace DiscreteStability
theorem _root_.solution (hH : LocalHyp f g xbar r₀ L) (hP : ∀ k, StepBound (P k) (lo k) (hi k))
    (hΛ : ∀ k, hi k ≤ Λ) (hS1 : L * Λ ≤ 2) (hH1 : IsolatedMax f xbar) {R : ℝ} (hR : 0 < R) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ R ∧ ρ ≤ r₀ ∧ (∀ y, y ≠ xbar → dist y xbar ≤ ρ → f y < f xbar) ∧
      ∃ δ > 0, ∀ (k₀ : ℕ) (x : ℕ → E), IsOrbit P g k₀ x → dist (x k₀) xbar < δ →
        ∀ k ≥ k₀, dist (x k) xbar < ρ ∧
          f (x k) + lo k * (2 - L * hi k) / 2 * ‖g (x k)‖ ^ 2 ≤ f (x (k + 1)) := by
  obtain ⟨r₁, hr₁, hmax⟩ := hH1
  have hgx := hH.grad_xbar_eq_zero ⟨r₁, hr₁, hmax⟩
  have hL := hH.L_nonneg
  set r := min R (min r₀ r₁) with hrdef
  have hr : 0 < r := lt_min hR (lt_min hH.r₀_pos hr₁)
  have hrR : r ≤ R := min_le_left _ _
  have hrr₀ : r ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₁ : r ≤ r₁ := (min_le_right _ _).trans (min_le_right _ _)
  set ρ := r / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  have hΛ0 : 0 ≤ Λ := (hP 0).hi_nonneg.trans (hΛ 0)
  have hLhi : ∀ k, L * hi k ≤ 2 := fun k =>
    (mul_le_mul_of_nonneg_left (hΛ k) hL).trans hS1
  -- each step from `B_ρ` stays in `B_r`
  have hseg : ∀ y k, dist y xbar < ρ → ∀ τ ∈ Icc (0 : ℝ) 1,
      dist (y + τ • P k (g y)) xbar < r := by
    intro y k hy τ hτ
    have hyb : y ∈ closedBall xbar r₀ := mem_closedBall.mpr (by linarith)
    have hxb : xbar ∈ closedBall xbar r₀ := mem_closedBall_self hH.r₀_pos.le
    have h1 : ‖g y‖ ≤ L * ‖y - xbar‖ := by
      have := hH.lip y hyb xbar hxb
      rwa [hgx, sub_zero] at this
    have h2 : ‖P k (g y)‖ ≤ Λ * ‖g y‖ :=
      ((hP k).norm_le _).trans (mul_le_mul_of_nonneg_right (hΛ k) (norm_nonneg _))
    have h3 : ‖P k (g y)‖ ≤ 2 * ‖y - xbar‖ := by
      calc ‖P k (g y)‖ ≤ Λ * ‖g y‖ := h2
        _ ≤ Λ * (L * ‖y - xbar‖) := mul_le_mul_of_nonneg_left h1 hΛ0
        _ = (L * Λ) * ‖y - xbar‖ := by ring
        _ ≤ 2 * ‖y - xbar‖ := mul_le_mul_of_nonneg_right hS1 (norm_nonneg _)
    rw [dist_eq_norm] at hy ⊢
    have e : y + τ • P k (g y) - xbar = (y - xbar) + τ • P k (g y) := by abel
    rw [e]
    calc ‖(y - xbar) + τ • P k (g y)‖ ≤ ‖y - xbar‖ + ‖τ • P k (g y)‖ := norm_add_le _ _
      _ = ‖y - xbar‖ + τ * ‖P k (g y)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
      _ ≤ ‖y - xbar‖ + 1 * (2 * ‖y - xbar‖) := by
          gcongr
          · exact hτ.2
      _ < r := by linarith
  -- weighted ascent at every point of `B_ρ`
  have hasc : ∀ y k, dist y xbar < ρ →
      f y + lo k * (2 - L * hi k) / 2 * ‖g y‖ ^ 2 ≤ f (y + P k (g y)) := by
    intro y k hy
    exact step_weighted (S := closedBall xbar r₀) (hP k) hL (hLhi k)
      (fun τ hτ => mem_closedBall.mpr ((hseg y k hy τ hτ).le.trans hrr₀)) hH.grad hH.lip
  -- the annulus `A = B̄_r \ B_ρ` and `m = min_A V > 0`
  have hA : IsCompact (closedBall xbar r \ ball xbar ρ) :=
    (isCompact_closedBall xbar r).diff isOpen_ball
  have hVc : ContinuousOn (fun y => f xbar - f y) (closedBall xbar r \ ball xbar ρ) :=
    continuousOn_const.sub (hH.continuousOn.mono
      (sdiff_subset.trans (closedBall_subset_closedBall hrr₀)))
  have hVpos : ∀ y ∈ closedBall xbar r \ ball xbar ρ, 0 < f xbar - f y := by
    intro y hy
    have hy1 : dist y xbar ≤ r := mem_closedBall.mp hy.1
    have hy2 : ρ ≤ dist y xbar := not_lt.mp (fun h => hy.2 (mem_ball.mpr h))
    have hne : y ≠ xbar := by
      intro h; rw [h, dist_self] at hy2; linarith
    linarith [hmax y hne (hy1.trans hrr₁)]
  obtain ⟨m, hm, hmA⟩ := exists_pos_lower_bound hA hVc hVpos
  -- `δ` with `V < m` on `B_δ`
  have hfc : ContinuousAt f xbar :=
    (hH.grad xbar (mem_closedBall_self hH.r₀_pos.le)).continuousAt
  obtain ⟨δ', hδ', hδ'f⟩ := Metric.continuousAt_iff.mp hfc m hm
  refine ⟨ρ, hρ, by linarith, by linarith,
    fun y hy hyd => hmax y hy (hyd.trans (by linarith)), min δ' ρ, lt_min hδ' hρ, ?_⟩
  intro k₀ x hx hx0
  -- invariant: `x k ∈ B_ρ` and `V(x k) < m`
  have hinv : ∀ k ≥ k₀, dist (x k) xbar < ρ ∧ f xbar - f (x k) < m := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      refine ⟨hx0.trans_le (min_le_right _ _), ?_⟩
      have := hδ'f (hx0.trans_le (min_le_left _ _))
      rw [Real.dist_eq] at this
      linarith [neg_abs_le (f (x k₀) - f xbar)]
    | succ k hk ih =>
      have hstep := hasc (x k) k ih.1
      rw [← hx k hk] at hstep
      have hw : 0 ≤ lo k * (2 - L * hi k) / 2 * ‖g (x k)‖ ^ 2 := by
        have := (hP k).lo_nonneg
        have := hLhi k
        have : 0 ≤ lo k * (2 - L * hi k) := mul_nonneg (hP k).lo_nonneg (by linarith)
        positivity
      have hV : f xbar - f (x (k + 1)) < m := by linarith [ih.2]
      refine ⟨?_, hV⟩
      have hr' : dist (x (k + 1)) xbar < r := by
        have := hseg (x k) k ih.1 1 ⟨zero_le_one, le_rfl⟩
        rwa [one_smul, ← hx k hk] at this
      by_contra hcon
      have hmem : x (k + 1) ∈ closedBall xbar r \ ball xbar ρ :=
        ⟨mem_closedBall.mpr hr'.le, fun h => hcon (mem_ball.mp h)⟩
      linarith [hmA _ hmem]
  intro k hk
  refine ⟨(hinv k hk).1, ?_⟩
  have := hasc (x k) k (hinv k hk).1
  rwa [← hx k hk] at this
end DiscreteStability
