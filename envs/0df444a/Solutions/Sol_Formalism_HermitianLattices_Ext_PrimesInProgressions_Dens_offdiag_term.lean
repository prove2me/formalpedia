-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.offdiag_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:20.875418+00:00
-- url     : https://prove2.me/submissions/bc14284e-861a-47d6-9514-3c5cb8c975f3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensDiv
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensBlock
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_char_mul_conj_self
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_char_mul_conj
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_natCast_cpow_neg_le_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_pair_cross_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_pair_same_bound


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
theorem _root_.solution {M : ℕ} [NeZero M] (σ T : ℝ) (U : ℕ) (hU : 1 ≤ U) (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ)
    (p p' : DirichletCharacter ℂ M × ℂ)
    (hp : σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T) (hp' : σ ≤ p'.2.re ∧ p'.2.re ≤ 1 ∧ |p'.2.im| ≤ T)
    (hsp : p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) :
    ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-((p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ))))‖ ≤
      (if p' = p then (U : ℝ) else 0) +
        (if p'.1 = p.1 then 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) else 0) +
        4 * ((M : ℝ) + 1) * (2 + 2 * T) := by
  obtain ⟨hl, hu, hi⟩ := hp
  obtain ⟨hl', hu', hi'⟩ := hp'
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  set w : ℂ := (p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ)) with hw
  have hwre : w.re = p.2.re + p'.2.re - 2 * σ := by
    simp only [hw, add_re, sub_re, ofReal_re, conj_re]; ring
  have hwim : w.im = p.2.im - p'.2.im := by
    simp only [hw, add_im, sub_im, ofReal_im, conj_im]; ring
  have hw0 : 0 ≤ w.re := by rw [hwre]; linarith
  have hw1 : w.re ≤ 1 := by rw [hwre]; linarith
  have hwn : ‖w‖ ≤ 1 + 2 * T := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_nonneg hw0, hwim]
    have : |p.2.im - p'.2.im| ≤ |p.2.im| + |p'.2.im| := abs_sub _ _
    linarith
  have hB : 4 * ((M : ℝ) + 1) * (1 + ‖w‖) ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T) := by
    have : 1 + ‖w‖ ≤ 2 + 2 * T := by linarith
    gcongr
  have hB0 : 0 ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hq0 : 0 ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) := by positivity
  by_cases h1 : p' = p
  · rw [if_pos h1, if_pos (by rw [h1])]
    have hdiag : ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-w)‖ ≤ U := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ n ∈ Ioc U (2 * U), ‖p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w)‖ ≤ 1 := by
        intro n hn
        have hn1 : 1 ≤ n := by have := (mem_Ioc.1 hn).1; omega
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have a1 : ‖p.1 (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have a2 : ‖p'.1 (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have a3 : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := norm_natCast_cpow_neg_le_one hn1 hw0
        calc ‖p.1 (n : ZMod M)‖ * ‖p'.1 (n : ZMod M)‖ * ‖(n : ℂ) ^ (-w)‖ ≤ 1 * 1 * 1 := by
              gcongr
          _ = 1 := by norm_num
      refine (sum_le_sum this).trans ?_
      rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
      exact_mod_cast (by omega : 2 * U - U ≤ U)
    linarith
  · rw [if_neg h1]
    by_cases h2 : p'.1 = p.1
    · rw [if_pos h2]
      have hgap : 1 ≤ |p.2.im - p'.2.im| := hsp (fun h => h1 h.symm) h2.symm
      have him : w.im ≠ 0 := by
        rw [hwim]; intro h0; rw [h0, abs_zero] at hgap; linarith
      have hsame := pair_same_bound M w hw0 hw1 him U hU
      have heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w) =
          ∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w) := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [h2, char_mul_conj_self]
      rw [heq]
      have hUp : (U : ℝ) ^ (1 - w.re) ≤ U := by
        calc (U : ℝ) ^ (1 - w.re) ≤ (U : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
          _ = U := Real.rpow_one _
      have hdiv : 4 * (U : ℝ) ^ (1 - w.re) / |w.im| ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) := by
        rw [hwim, mul_one_div]
        gcongr
      linarith
    · rw [if_neg h2]
      have hne : p.1 * p'.1⁻¹ ≠ 1 := by
        intro h; exact h2 (mul_inv_eq_one.1 h).symm
      have hcross := pair_cross_bound M (p.1 * p'.1⁻¹) hne w hw0 U hU
      have heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w) =
          ∑ n ∈ Ioc U (2 * U), (p.1 * p'.1⁻¹) (n : ZMod M) * (n : ℂ) ^ (-w) := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [char_mul_conj]
      rw [heq]
      linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
