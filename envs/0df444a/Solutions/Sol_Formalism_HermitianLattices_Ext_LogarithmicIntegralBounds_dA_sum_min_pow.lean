-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_min_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:57.989275+00:00
-- url     : https://prove2.me/submissions/a9c2bbad-93c4-4a0c-8e29-b8267c20bc70

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_sum_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_tail_geo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
open ArithmeticFunction (vonMangoldt)
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (x : ℝ) (hx : 1 ≤ x) (p : ℕ) (hp : 2 ≤ p) (L : ℕ) :
    Real.log p * ∑ i ∈ Icc 1 L, min 1 (x / (p : ℝ) ^ i) ≤ Real.log x + 2 * Real.log p := by
  have hp0 : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hx0 : (0:ℝ) < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set T := ⌊Real.log x / Real.log p⌋₊ + 1 with hT
  have hTlt : Real.log x / Real.log p < (T:ℝ) := by
    rw [hT]
    push_cast
    exact Nat.lt_floor_add_one _
  have hTle : (T:ℝ) - 1 ≤ Real.log x / Real.log p := by
    rw [hT]
    push_cast
    linarith [Nat.floor_le (div_nonneg hlx hlp.le)]
  have hTlog : ((T:ℝ) - 1) * Real.log p ≤ Real.log x := (le_div_iff₀ hlp).mp hTle
  have hxT : x ≤ (p:ℝ) ^ T := by
    have h1 : Real.log x < Real.log ((p:ℝ) ^ T) := by
      rw [Real.log_pow]
      rwa [div_lt_iff₀ hlp] at hTlt
    exact ((Real.log_lt_log_iff hx0 (by positivity)).mp h1).le
  have hr0 : (0:ℝ) ≤ 1 / p := by positivity
  have hr : (1:ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp0
  have htail : ∀ M, T ≤ M → ∑ i ∈ Ioc T M, min 1 (x / (p:ℝ) ^ i) ≤ 1 := by
    intro M hM
    have hg := dA_tail_geo (1 / (p:ℝ)) hr0 hr T M hM
    have hpos : (0:ℝ) ≤ (1 / (p:ℝ)) ^ M := pow_nonneg hr0 M
    calc ∑ i ∈ Ioc T M, min 1 (x / (p:ℝ) ^ i) ≤ ∑ i ∈ Ioc T M, x * (1 / (p:ℝ)) ^ i :=
          Finset.sum_le_sum (fun i _ => (min_le_right _ _).trans
            (le_of_eq (by rw [one_div_pow, mul_one_div])))
      _ = x * ∑ i ∈ Ioc T M, (1 / (p:ℝ)) ^ i := by rw [Finset.mul_sum]
      _ ≤ x * (1 / (p:ℝ)) ^ T := mul_le_mul_of_nonneg_left (by linarith) hx0.le
      _ = x / (p:ℝ) ^ T := by rw [one_div_pow, mul_one_div]
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hxT
  have hsplit := dA_sum_split (fun i => min 1 (x / (p:ℝ) ^ i))
    (fun i => le_min zero_le_one (div_nonneg hx0.le (by positivity)))
    (fun i => min_le_left _ _) T 1 htail L
  have hmul := mul_le_mul_of_nonneg_left hsplit hlp.le
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
