-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.dyadic_block_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:35.084909+00:00
-- url     : https://prove2.me/submissions/00e9c965-3923-40e2-971f-ffb0a5bc99a0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensDiv
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensBlock
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_conj_natCast_cpow_neg__5ffeb6974682
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_coefficient_block_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_duality_inequality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution : BlockCnt := by
  intro α S f ρ Y N U σ θ G K hU hθ hσ hG hK hf hρ hoff hlarge hsmall
  set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(σ : ℂ)) with hb
  set v : α → ℕ → ℂ := fun p n => f p n * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) with hv
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hbv : ∀ p, ∀ n ∈ Ioc U (2 * U), b n * v p n = mco Y N n * f p n * (n : ℂ) ^ (-ρ p) := by
    intro p n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
    have : (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) = (n : ℂ) ^ (-ρ p) := by
      rw [← Complex.cpow_add _ _ hn0]; congr 1; ring
    simp only [hb, hv]
    rw [← this]; ring
  have hsum : ∀ p, ∑ n ∈ Ioc U (2 * U), b n * v p n = blkD Y N U (f p) (ρ p) := by
    intro p; unfold blkD; exact sum_congr rfl (hbv p)
  have heq : ∀ p p', ∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n) =
      ∑ n ∈ Ioc U (2 * U), f p n * (starRingEnd ℂ) (f p' n) *
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ)))) := by
    intro p p'
    refine sum_congr rfl (fun n hn => ?_)
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
    simp only [hv]
    rw [map_mul, conj_natCast_cpow_neg']
    have : (n : ℂ) ^ (-(ρ p - (σ : ℂ))) * (n : ℂ) ^ (-(starRingEnd ℂ) (ρ p' - (σ : ℂ))) =
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ)))) := by
      rw [← Complex.cpow_add _ _ hn0]; congr 1; ring
    rw [← this]; ring
  have hΔ : ∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n)‖ ≤
      (U : ℝ) * G + (S.card : ℝ) * K := by
    intro p hp
    simp only [heq]
    exact hoff p hp
  have hΔ0 : (0 : ℝ) ≤ (U : ℝ) * G + (S.card : ℝ) * K := by positivity
  have hmain := duality_inequality α ℕ S (Ioc U (2 * U)) b v _ hΔ0 hΔ
  simp only [hsum] at hmain
  set a : ℝ := 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 with ha
  have hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ a := by
    refine le_trans (le_of_eq ?_) (coefficient_block_bound Y N U σ hU hσ)
    refine sum_congr rfl (fun n hn => ?_)
    have hn1 : 0 < n := by have := (mem_Ioc.1 hn).1; omega
    simp only [hb, norm_mul, norm_natCast_cpow_of_pos hn1, neg_re, ofReal_re]
  have hlow : (S.card : ℝ) * θ ^ 2 ≤ ∑ p ∈ S, ‖blkD Y N U (f p) (ρ p)‖ ^ 2 := by
    have : ∀ p ∈ S, θ ^ 2 ≤ ‖blkD Y N U (f p) (ρ p)‖ ^ 2 := by
      intro p hp
      exact pow_le_pow_left₀ hθ.le (hlarge p hp) 2
    have h := sum_le_sum this
    rw [sum_const, nsmul_eq_mul] at h
    exact h
  have haU : a * U = 2 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 := by
    have : (U : ℝ) ^ (2 - 2 * σ) = (U : ℝ) ^ (1 - 2 * σ) * (U : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hU0]; congr 1; ring
    rw [this, Real.rpow_one, ha]; ring
  have h1 : (S.card : ℝ) * θ ^ 2 ≤ a * ((U : ℝ) * G + (S.card : ℝ) * K) :=
    hlow.trans (hmain.trans (mul_le_mul_of_nonneg_right hbn hΔ0))
  have hS0 : (0 : ℝ) ≤ S.card := by positivity
  have h2 : (S.card : ℝ) * θ ^ 2 ≤ 2 * (a * U) * G := by
    have := mul_le_mul_of_nonneg_left hsmall hS0
    nlinarith
  have hθ2 : 0 < θ ^ 2 := by positivity
  rw [le_div_iff₀ hθ2]
  rw [haU] at h2
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
