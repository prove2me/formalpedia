-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:42.889149+00:00
-- url     : https://prove2.me/submissions/dc7b6acb-85c2-4938-be4c-001b70a42547

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplPick
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplNeg
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplEdge
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_rpow_sigma
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_horiz_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_left_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_negLD_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_rect_Fchi
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_tail_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_alg
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_ge_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_y
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_norm
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_formula_character


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
theorem _root_.solution : ∃ C₂ C₃ : ℝ, 0 < C₂ ∧ 0 ≤ C₃ ∧ ∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 20 →
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T σ₁ T' δ : ℝ), 3 ≤ M → 2 ≤ T →
    1 - κ ≤ σ₁ → σ₁ ≤ 1 - 3 * κ / 4 → T ≤ T' → T' ≤ T + 1 → 0 < δ → δ ≤ 1 / 20 →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → |ρ.im| ≤ T + 3 → δ ≤ |σ₁ - ρ.re|) →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → δ ≤ |(|ρ.im| - T')|) →
    ∀ Z : Finset ℂ, (∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T')) →
    ∀ y : ℝ, 2 ≤ y →
      ‖Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - explicitFormulaConstant χ - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤
        1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T' +
          2 * T' * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁)) +
          (3 * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 1) * (Real.exp 1 * y) / T' ^ 2 +
           3 * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 1) * (Real.exp 1 * y) / T' ^ 2)) := by
  obtain ⟨C₂, hC₂, hneg⟩ := ex_negLD_bound
  obtain ⟨C₃, hC₃, htail⟩ := ex_tail_bound
  refine ⟨C₂, C₃, hC₂, hC₃, ?_⟩
  intro κ hκ hκ' M _ χ T σ₁ T' δ hM hT hσ hσ' hTT' hT'T hδ0 hδ' hgapre hgapim Z hZ y hy
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hy0 : 0 < y := by linarith
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have hly := exm_log_y y hy
  have hl1 := exm_log_ge_one (M : ℝ) T hM' hT
  set N := C₂ * (2 * Real.log ((M : ℝ) * T)) / δ with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  set σ₀ := 1 + 1 / Real.log y with hσ₀
  have hσ₀1 : 1 < σ₀ := by
    have : 0 < 1 / Real.log y := by positivity
    linarith
  have hσ₀3 : σ₀ ≤ 3 := by
    have : 1 / Real.log y ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hly
    rw [hσ₀]; linarith
  have hyσ₀ : y ^ σ₀ = Real.exp 1 * y := exm_rpow_sigma y hy
  have hσ19 : 19 / 20 ≤ σ₁ := by linarith
  have hσ1 : σ₁ < 1 := by linarith
  have hT'0 : 0 < T' := by linarith

  have hBL : ∀ t : ℝ, |t| ≤ T' → ‖negLD χ ((σ₁ : ℂ) + t * I)‖ ≤ N + 4 / (3 * κ) := by
    intro t ht
    have hre : ((σ₁ : ℂ) + t * I).re = σ₁ := by simp
    have him : ((σ₁ : ℂ) + t * I).im = t := by simp
    have hnorm : 3 * κ / 4 ≤ ‖(σ₁ : ℂ) + t * I - 1‖ := by
      have h1 := Complex.abs_re_le_norm ((σ₁ : ℂ) + t * I - 1)
      have h2 : ((σ₁ : ℂ) + t * I - 1).re = σ₁ - 1 := by simp
      rw [h2, abs_of_neg (by linarith)] at h1
      linarith
    have hne : (σ₁ : ℂ) + t * I ≠ 1 := by
      intro h
      rw [h] at hnorm
      simp at hnorm
      linarith
    apply exm_neg hC₂ χ T δ _ _ hM hT hδ0 (by rw [him]; linarith) _ (by positivity)
    · apply hneg M χ _ δ hM hδ0 hδ' (by rw [hre]; exact hσ19) (by rw [hre]; linarith) hne
      intro ρ hρ hρre hρs
      have h1 := Complex.abs_re_le_norm (ρ - ((σ₁ : ℂ) + t * I))
      have h2 := Complex.abs_im_le_norm (ρ - ((σ₁ : ℂ) + t * I))
      rw [Complex.sub_re, hre] at h1
      rw [Complex.sub_im, him] at h2
      have h3 : |ρ.im| ≤ T + 3 := by
        have : |ρ.im| ≤ |ρ.im - t| + |t| := by
          have := abs_add_le (ρ.im - t) t
          simpa using this
        linarith
      have h4 := hgapre ρ hρ hρre h3
      rw [abs_sub_comm] at h4
      linarith
    · have := one_div_le_one_div_of_le (by positivity : 0 < 3 * κ / 4) hnorm
      rwa [one_div_div] at this

  have hBH : ∀ v : ℝ, |v| = T' → ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₀ → ‖negLD χ ((x : ℂ) + v * I)‖ ≤ N + 1 := by
    intro v hv x hx hx'
    have hre : ((x : ℂ) + v * I).re = x := by simp
    have him : ((x : ℂ) + v * I).im = v := by simp
    have hnorm : 1 ≤ ‖(x : ℂ) + v * I - 1‖ := by
      have h1 := Complex.abs_im_le_norm ((x : ℂ) + v * I - 1)
      have h2 : ((x : ℂ) + v * I - 1).im = v := by simp
      rw [h2, hv] at h1
      linarith
    have hne : (x : ℂ) + v * I ≠ 1 := by
      intro h
      rw [h] at hnorm
      simp at hnorm
      linarith
    apply exm_neg hC₂ χ T δ _ _ hM hT hδ0 (by rw [him, hv]; linarith) _ (by norm_num)
    · apply hneg M χ _ δ hM hδ0 hδ' (by rw [hre]; linarith) (by rw [hre]; linarith) hne
      intro ρ hρ hρre _
      have h2 := Complex.abs_im_le_norm (ρ - ((x : ℂ) + v * I))
      rw [Complex.sub_im, him] at h2
      have h4 := hgapim ρ hρ hρre
      rw [← hv] at h4
      have h5 := abs_abs_sub_abs_le ρ.im v
      linarith
    · have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnorm
      simpa using this
  have hH : ∀ v : ℝ, |v| = T' → ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + v * I)‖ ≤
      3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2 := by
    intro v hv
    have h := ex_horiz_bound χ y σ₁ σ₀ v (N + 1) (by linarith) (by linarith) (by rw [hv]; linarith)
      (by linarith) (hBH v hv)
    have hv2 : v ^ 2 = T' ^ 2 := by rw [← hv, sq_abs]
    rw [hv2, hyσ₀] at h
    refine h.trans ?_
    have : σ₀ - σ₁ ≤ 3 := by linarith
    gcongr
  have hLf := ex_left_bound χ y σ₁ T' (N + 4 / (3 * κ)) (by linarith) (by linarith) hσ1 hT'0.le hBL
  have hTl := htail M χ y σ₀ T' (by linarith) hσ₀1 (by linarith)
  have hinv : 1 / (σ₀ - 1) = Real.log y := by rw [hσ₀]; simp
  rw [hinv, hyσ₀] at hTl
  have hedge : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ |w.im| < T' := by
    intro w hw1 _ hw3 hw0
    have h1 := hgapre w hw0 (by linarith) (by linarith)
    have h2 := hgapim w hw0 (by linarith)
    constructor
    · rcases hw1.lt_or_eq with h | h
      · exact h
      · rw [h] at h1; simp at h1; linarith
    · rcases hw3.lt_or_eq with h | h
      · exact h
      · rw [h] at h2; simp at h2; linarith
  have hrect := ex_rect_Fchi χ y hy0 σ₁ σ₀ T' (by linarith) hσ1 hσ₀1 hT'0 Z hZ hedge
  have hper := (perron_formula_character M χ y (by linarith) σ₀ hσ₀1).2
  unfold Formalism.ZF.rectInt at hrect
  have halg := exm_alg _ _ _ _ _ _ _ _ _ y hy0 hper hrect
  have hD : (if χ = 1 then (y : ℂ) * (Real.log y : ℂ) - y else 0) / (y : ℂ) =
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) := by
    split_ifs
    · push_cast; field_simp
    · simp
  have hS : (∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ) / (y : ℂ) =
      ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [exKer, Complex.cpow_sub _ _ hyC, Complex.cpow_one]
    ring
  rw [hD, hS] at halg
  rw [halg]
  exact exm_norm _ _ _ _ _ y _ _ _ _ hy0 hTl hLf (hH (-T') (by rw [abs_neg, abs_of_pos hT'0]))
    (hH T' (abs_of_pos hT'0))
end Formalism.HermitianLattices.Ext.PrimesInProgressions
