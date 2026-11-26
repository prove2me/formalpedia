-- Prove2me | solution 1 for FriedCrossing.PureZeros.hasDerivAt_zero_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:59:27.765475+00:00
-- url     : https://prove2.me/submissions/417c44b7-f359-4e12-b8cb-ab3655009360

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_PureZeros_hasDerivAt_wMinus
import Theorems.Thm_FriedCrossing_PureZeros_continuousAt_wMinus
import Theorems.Thm_FriedCrossing_PureZeros_dwMinus_at_zero
import Theorems.Thm_FriedCrossing_PureZeros_dwPlus_at_zero
import Theorems.Thm_FriedCrossing_PureZeros_wPlus_at_zero_pos
import Theorems.Thm_FriedCrossing_PureZeros_wMinus_at_zero_neg
import Theorems.Thm_FriedCrossing_TwinRate_cluster_roots
import Theorems.Thm_FriedCrossing_TwinRate_continuousAt_wPlus
import Theorems.Thm_FriedCrossing_TwinRate_hasDerivAt_wPlus


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {e₁ e₂ z : ℝ → ℝ} {e₁' e₂' σ : ℝ}
    (hd₁ : HasDerivAt e₁ e₁' σ) (hd₂ : HasDerivAt e₂ e₂' σ)
    (h₂σ : e₂ σ = 0) (h₁σ : e₁ σ ≠ 0)
    (hzQ : ∀ τ, 0 ≤ disc (e₁ τ) (e₂ τ) → z τ ^ 2 - e₁ τ * z τ + e₂ τ = 0)
    (hzc : ContinuousAt z σ) (hz0 : z σ = 0) :
    HasDerivAt z (e₂' / e₁ σ) σ := by
  have hc₁ : ContinuousAt e₁ σ := hd₁.continuousAt
  have hc₂ : ContinuousAt e₂ σ := hd₂.continuousAt
  have hpair : ContinuousAt (fun τ => (e₁ τ, e₂ τ)) σ := hc₁.prodMk hc₂
  have hDσ : 0 < disc (e₁ σ) (e₂ σ) := by
    unfold disc; rw [h₂σ, mul_zero, sub_zero]; positivity
  have hDc : ContinuousAt (fun τ => disc (e₁ τ) (e₂ τ)) σ := by
    unfold disc
    exact (hc₁.pow 2).sub (continuousAt_const.mul hc₂)
  have hevD : ∀ᶠ τ in 𝓝 σ, 0 < disc (e₁ τ) (e₂ τ) := hDc.eventually (lt_mem_nhds hDσ)
  -- z is one of the two explicit roots wherever the discriminant is nonnegative
  have hroots : ∀ τ, 0 ≤ disc (e₁ τ) (e₂ τ) →
      z τ = wPlus (e₁ τ) (e₂ τ) ∨ z τ = wMinus (e₁ τ) (e₂ τ) := fun τ hD => by
    have h := (TwinRate.cluster_roots (sStar := 0) (τ := 1) hD (z τ)).mp
    simp only [TwinRate.clusterTrace, TwinRate.clusterDet, mul_zero, zero_add, one_mul,
      zero_mul, add_zero, one_pow, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_one] at h
    exact h (hzQ τ hD)
  rcases lt_or_gt_of_ne h₁σ with hneg | hpos
  · -- e₁(σ) < 0: the root through 0 is w₊; w₋(σ) = e₁(σ) < 0
    have hwP : ContinuousAt (fun τ => wPlus (e₁ τ) (e₂ τ)) σ :=
      (continuousAt_wPlus _).comp hpair
    have hwM : ContinuousAt (fun τ => wMinus (e₁ τ) (e₂ τ)) σ :=
      (continuousAt_wMinus _).comp hpair
    have hwMσ : wMinus (e₁ σ) (e₂ σ) = e₁ σ := by rw [h₂σ]; exact wMinus_at_zero_neg hneg
    have hevM : ∀ᶠ τ in 𝓝 σ, wMinus (e₁ τ) (e₂ τ) < e₁ σ / 2 :=
      hwM.eventually_lt continuousAt_const
        (by change wMinus (e₁ σ) (e₂ σ) < e₁ σ / 2; rw [hwMσ]; linarith)
    have hevz : ∀ᶠ τ in 𝓝 σ, e₁ σ / 2 < z τ :=
      continuousAt_const.eventually_lt hzc (by change e₁ σ / 2 < z σ; rw [hz0]; linarith)
    have heq : z =ᶠ[𝓝 σ] fun τ => wPlus (e₁ τ) (e₂ τ) := by
      filter_upwards [hevD, hevM, hevz] with τ hD hM hz
      rcases hroots τ hD.le with h | h
      · exact h
      · exfalso; rw [h] at hz; linarith
    have hderiv : HasDerivAt (fun τ => wPlus (e₁ τ) (e₂ τ))
        (dwPlus (e₁ σ) (e₂ σ) e₁' e₂') σ := hasDerivAt_wPlus hd₁ hd₂ hDσ
    rw [h₂σ, dwPlus_at_zero hneg] at hderiv
    exact hderiv.congr_of_eventuallyEq heq
  · -- e₁(σ) > 0: the root through 0 is w₋; w₊(σ) = e₁(σ) > 0
    have hwP : ContinuousAt (fun τ => wPlus (e₁ τ) (e₂ τ)) σ :=
      (continuousAt_wPlus _).comp hpair
    have hwPσ : wPlus (e₁ σ) (e₂ σ) = e₁ σ := by rw [h₂σ]; exact wPlus_at_zero_pos hpos
    have hevP : ∀ᶠ τ in 𝓝 σ, e₁ σ / 2 < wPlus (e₁ τ) (e₂ τ) :=
      continuousAt_const.eventually_lt hwP
        (by change e₁ σ / 2 < wPlus (e₁ σ) (e₂ σ); rw [hwPσ]; linarith)
    have hevz : ∀ᶠ τ in 𝓝 σ, z τ < e₁ σ / 2 :=
      hzc.eventually_lt continuousAt_const (by change z σ < e₁ σ / 2; rw [hz0]; linarith)
    have heq : z =ᶠ[𝓝 σ] fun τ => wMinus (e₁ τ) (e₂ τ) := by
      filter_upwards [hevD, hevP, hevz] with τ hD hP hz
      rcases hroots τ hD.le with h | h
      · exfalso; rw [h] at hz; linarith
      · exact h
    have hderiv : HasDerivAt (fun τ => wMinus (e₁ τ) (e₂ τ))
        (dwMinus (e₁ σ) (e₂ σ) e₁' e₂') σ := hasDerivAt_wMinus hd₁ hd₂ hDσ
    rw [h₂σ, dwMinus_at_zero hpos] at hderiv
    exact hderiv.congr_of_eventuallyEq heq
end FriedCrossing.PureZeros
