-- Prove2me | solution 1 for FriedCrossing.Branch.zBranch_at_simple_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:03:07.629154+00:00
-- url     : https://prove2.me/submissions/3881fc89-484e-4378-b1c6-36e530c5accf

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_PureZeros_continuousAt_wMinus
import Theorems.Thm_FriedCrossing_PureZeros_wMinus_at_zero_neg
import Theorems.Thm_FriedCrossing_PureZeros_wMinus_at_zero_nonneg
import Theorems.Thm_FriedCrossing_PureZeros_wPlus_at_zero_neg
import Theorems.Thm_FriedCrossing_PureZeros_wPlus_at_zero_pos
import Theorems.Thm_FriedCrossing_TwinRate_continuousAt_wPlus


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Branch
open TwinRate PureZeros
namespace FriedCrossing.Branch
theorem _root_.solution {e₁ e₂ : ℝ → ℝ} {σ : ℝ} (hc₁ : ContinuousAt e₁ σ)
    (hc₂ : ContinuousAt e₂ σ) (h₂ : e₂ σ = 0) (h₁ : e₁ σ ≠ 0) :
    ContinuousAt (zBranch e₁ e₂) σ ∧ zBranch e₁ e₂ σ = 0 := by
  have hpair : ContinuousAt (fun τ => (e₁ τ, e₂ τ)) σ := hc₁.prodMk hc₂
  have hwP : ContinuousAt (fun τ => wPlus (e₁ τ) (e₂ τ)) σ := (continuousAt_wPlus _).comp hpair
  have hwM : ContinuousAt (fun τ => wMinus (e₁ τ) (e₂ τ)) σ := (continuousAt_wMinus _).comp hpair
  have habsP : ContinuousAt (fun τ => |wPlus (e₁ τ) (e₂ τ)|) σ :=
    continuous_abs.continuousAt.comp hwP
  have habsM : ContinuousAt (fun τ => |wMinus (e₁ τ) (e₂ τ)|) σ :=
    continuous_abs.continuousAt.comp hwM
  have hhalf : 0 < |e₁ σ| / 2 := by have := abs_pos.mpr h₁; linarith
  rcases lt_or_gt_of_ne h₁ with hneg | hpos
  · -- e₁(σ) < 0: w₊(σ) = 0 is the branch through 0, w₋(σ) = e₁(σ)
    have hPσ : wPlus (e₁ σ) (e₂ σ) = 0 := by rw [h₂]; exact wPlus_at_zero_neg hneg
    have hMσ : wMinus (e₁ σ) (e₂ σ) = e₁ σ := by rw [h₂]; exact wMinus_at_zero_neg hneg
    have h1 : ∀ᶠ τ in 𝓝 σ, |wPlus (e₁ τ) (e₂ τ)| < |e₁ σ| / 2 :=
      habsP.eventually (gt_mem_nhds (by
        change |wPlus (e₁ σ) (e₂ σ)| < _; rw [hPσ, abs_zero]; exact hhalf))
    have h2 : ∀ᶠ τ in 𝓝 σ, |e₁ σ| / 2 < |wMinus (e₁ τ) (e₂ τ)| :=
      habsM.eventually (lt_mem_nhds (by
        change _ < |wMinus (e₁ σ) (e₂ σ)|; rw [hMσ]; linarith))
    have heq : (fun τ => wPlus (e₁ τ) (e₂ τ)) =ᶠ[𝓝 σ] zBranch e₁ e₂ := by
      filter_upwards [h1, h2] with τ hτ1 hτ2
      simp only [zBranch]; rw [if_pos (le_of_lt (lt_trans hτ1 hτ2))]
    refine ⟨hwP.congr heq, ?_⟩
    simp only [zBranch]
    rw [if_pos (by rw [hPσ, abs_zero]; exact abs_nonneg _), hPσ]
  · -- e₁(σ) > 0: w₋(σ) = 0 is the branch through 0, w₊(σ) = e₁(σ)
    have hPσ : wPlus (e₁ σ) (e₂ σ) = e₁ σ := by rw [h₂]; exact wPlus_at_zero_pos hpos
    have hMσ : wMinus (e₁ σ) (e₂ σ) = 0 := by rw [h₂]; exact wMinus_at_zero_nonneg hpos.le
    have h1 : ∀ᶠ τ in 𝓝 σ, |wMinus (e₁ τ) (e₂ τ)| < |e₁ σ| / 2 :=
      habsM.eventually (gt_mem_nhds (by
        change |wMinus (e₁ σ) (e₂ σ)| < _; rw [hMσ, abs_zero]; exact hhalf))
    have h2 : ∀ᶠ τ in 𝓝 σ, |e₁ σ| / 2 < |wPlus (e₁ τ) (e₂ τ)| :=
      habsP.eventually (lt_mem_nhds (by
        change _ < |wPlus (e₁ σ) (e₂ σ)|; rw [hPσ]; linarith))
    have heq : (fun τ => wMinus (e₁ τ) (e₂ τ)) =ᶠ[𝓝 σ] zBranch e₁ e₂ := by
      filter_upwards [h1, h2] with τ hτ1 hτ2
      simp only [zBranch]; rw [if_neg (not_le.mpr (lt_trans hτ1 hτ2))]
    refine ⟨hwM.congr heq, ?_⟩
    simp only [zBranch]
    rw [if_neg (by rw [hPσ, hMσ, abs_zero]; exact not_le.mpr (abs_pos.mpr h₁)), hMσ]
end FriedCrossing.Branch
