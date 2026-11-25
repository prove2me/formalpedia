-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.smoothed_explicit_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:06.268526+00:00
-- url     : https://prove2.me/submissions/62afaf62-b7ef-4e95-9e86-41b3dd1ae90a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplPick
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplNeg
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplEdge
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMain
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_deriv_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exOrd_eq_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exOrd_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_box
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_choose
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_N_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_core
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_horiz_num
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_left_num
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_ge_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_y
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_tail_num
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_isLZero_iff_exLF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sum_le_mul_rpow_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : ExplicitS := by
  intro κ hκ hκ'
  obtain ⟨C₁, hC₁, hch⟩ := ex_choose
  obtain ⟨C₄, hC₄, hbox⟩ := ex_box
  obtain ⟨C₂, C₃, hC₂, hC₃, hcore⟩ := exm_core
  set G := 6 * C₁ * C₂ / κ with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  set AL := 3 * (G + 4 / (3 * κ)) * (2 / κ) with hAL
  set AW := (1 + 2 * C₃) + (3 * (G + 1) + 3 * (G + 1)) with hAW
  set C := max (max 4 C₄) (max AL AW) with hC
  have hC4 : 4 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCC₄ : C₄ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCL : AL ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCW : AW ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, by linarith, ?_⟩
  intro M _ χ T hM hT
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨σ₁, T', δ, hσ, hσ', hTT', hT'T, hδ0, hδ', hδlow, hgapre, hgapim⟩ := hch κ hκ hκ' M χ T hM hT
  obtain ⟨Z₀, hZ₀, hwin, _⟩ := hbox M χ (T + 1) hM (by linarith)
  have hZ : ∀ ρ : ℂ, ρ ∈ Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T') ↔
      (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T') := by
    intro ρ
    rw [Finset.mem_filter, hZ₀]
    constructor
    · rintro ⟨⟨h0, _, _⟩, h1, h2⟩
      exact ⟨h0, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, by linarith, by linarith⟩, h1, h2⟩
  refine ⟨Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T'), exOrd χ, explicitFormulaConstant χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨h0, h1, h2⟩ := (hZ ρ).1 hρ
    exact ⟨(isLZero_iff_exLF χ ρ).2 h0, by linarith, by linarith⟩
  · intro ρ hρ hre him
    have h0 := (isLZero_iff_exLF χ ρ).1 hρ
    refine (hZ ρ).2 ⟨h0, by linarith, ?_⟩
    have h2 := hgapim ρ h0 (by linarith)
    rcases (him.trans hTT').lt_or_eq with h | h
    · exact h
    · rw [h] at h2; simp at h2; linarith
  · intro ρ hρ
    exact exOrd_pos χ ((hZ ρ).1 hρ).1
  · intro ρ hρ hd
    have h0 := ((hZ ρ).1 hρ).1
    exact exOrd_eq_one χ h0 (exLF_deriv_ne_zero χ h0 hd)
  · intro t
    have hsub : (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1) ⊆
        Z₀.filter (fun ρ => |ρ.im - t| ≤ 1) :=
      Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    have h1 : (∑ ρ ∈ (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1),
        exOrd χ ρ) ≤ ∑ ρ ∈ Z₀.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ :=
      Finset.sum_le_sum_of_subset hsub
    have h2 : (0 : ℝ) ≤ Real.log ((M : ℝ) * (|t| + 2)) := by
      apply Real.log_nonneg
      have := abs_nonneg t
      nlinarith
    calc ((∑ ρ ∈ (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1),
        exOrd χ ρ : ℕ) : ℝ) ≤ ((∑ ρ ∈ Z₀.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ C₄ * Real.log ((M : ℝ) * (|t| + 2)) := hwin t
      _ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) := by gcongr
  · intro y hy
    have hmain := hcore κ hκ hκ' M χ T σ₁ T' δ hM hT hσ hσ' hTT' hT'T hδ0 hδ' hgapre hgapim _ hZ y hy
    refine hmain.trans ?_
    have hl1 := exm_log_ge_one (M : ℝ) T hM' hT
    have hNle := exm_N_le κ C₁ C₂ (M : ℝ) T δ hκ hC₁ hC₂ hM' hT hδ0 hδlow
    rw [← hG] at hNle
    set N := C₂ * (2 * Real.log ((M : ℝ) * T)) / δ with hN
    have hN0 : 0 ≤ N := by rw [hN]; positivity
    have ht := exm_tail_num C₃ T T' y (Real.log ((M : ℝ) * T)) hC₃ hT hTT' hy hl1
    have hh := exm_horiz_num G N T T' y (Real.log ((M : ℝ) * T)) hG0 hN0 hNle hT hTT' hy hl1
    have hl := exm_left_num κ G N (M : ℝ) T T' σ₁ y hκ hκ' hG0 hN0 hNle hM' hT hTT' hT'T hσ hσ' hy
    have hy0 : 0 < y := by linarith
    have hly := exm_log_y y hy
    have hX : 1 ≤ (M : ℝ) * T := by nlinarith
    have hfin := sum_le_mul_rpow_add AL AW C ((M : ℝ) * T) (y ^ (-(κ / 2)))
      (Real.log y * Real.log ((M : ℝ) * T) ^ 2 / T) hC4 hCL hCW hX (Real.rpow_nonneg hy0.le _)
      (by have : 0 < T := by linarith
          positivity)
    refine le_trans ?_ hfin
    have hsum := add_le_add (add_le_add ht hl) (add_le_add hh hh)
    calc _ = _ := by ring
      _ ≤ _ := hsum
      _ = _ := by rw [hAW, hAL]; ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
