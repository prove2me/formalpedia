-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.coefficient_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:32:07.703151+00:00
-- url     : https://prove2.me/submissions/2ac82671-015d-4484-acf2-7e886c317d9c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensDiv
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_divisor_square_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mco_norm_le


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
theorem _root_.solution : CoefficientBlockBound := by
  intro Y N U σ hU hσ
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hterm : ∀ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2 ≤
      (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hUn : (U : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have h1 : ‖mco Y N n‖ ≤ (n.divisors.card : ℝ) := mco_norm_le Y N hn1
    have h2 : (n : ℝ) ^ (-σ) ≤ (U : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hU0 hUn (by linarith)
    have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h4 : ((U : ℝ) ^ (-σ)) ^ 2 = (U : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
      congr 1
      push_cast
      ring
    calc (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2
        ≤ ((n.divisors.card : ℝ) * (U : ℝ) ^ (-σ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) h3)
            (mul_le_mul h1 h2 h3 (Nat.cast_nonneg _)) 2
      _ = (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
          rw [mul_pow, h4, mul_comm]
  have hsub : Ioc U (2 * U) ⊆ Icc 1 (2 * U) := by
    intro n hn
    rw [mem_Ioc] at hn
    rw [mem_Icc]
    omega
  have hD := divisor_square_bound (2 * U) (by omega)
  have hpow : (U : ℝ) ^ (1 - 2 * σ) = (U : ℝ) ^ (-(2 * σ)) * U := by
    rw [show (1 - 2 * σ) = -(2 * σ) + 1 by ring, Real.rpow_add hU0, Real.rpow_one]
  calc ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2
      ≤ ∑ n ∈ Ioc U (2 * U), (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := sum_le_sum hterm
    _ = (U : ℝ) ^ (-(2 * σ)) * ∑ n ∈ Ioc U (2 * U), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ (U : ℝ) ^ (-(2 * σ)) * ∑ n ∈ Icc 1 (2 * U), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hU0.le _)
        exact sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ ≤ (U : ℝ) ^ (-(2 * σ)) * (((2 * U : ℕ) : ℝ) * (1 + Real.log ((2 * U : ℕ) : ℝ)) ^ 3) :=
        mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hU0.le _)
    _ = 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 := by
        rw [hpow]
        push_cast
        ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
