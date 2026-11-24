-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.rank_mul_pow_three_halves_le_fourth_power
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:19.511186+00:00
-- url     : https://prove2.me/submissions/3c363ec3-aff9-428f-9749-363865ff24d8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : RankMulPowThreeHalvesLeFourthPower := by
  intro f m k L hm hmf hk hL
  have hr3 : (3 : ℝ) ≤ ((k + m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + m - 1)
  have hq1 : (1 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m / 2)
  have hqf : 2 * ((m / 2 : ℕ) : ℝ) ≤ (f : ℝ) := by exact_mod_cast (by omega : 2 * (m / 2) ≤ f)
  have hf2 : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast (by omega : 2 ≤ f)
  set r : ℝ := ((k + m - 1 : ℕ) : ℝ)
  set q : ℝ := ((m / 2 : ℕ) : ℝ)
  have hpow : q ^ ((3 : ℝ) / 2) ≤ q ^ 2 := by
    rw [← Real.rpow_natCast q 2]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have hq2 : q ^ 2 ≤ (f : ℝ) ^ 2 / 4 := by
    nlinarith [mul_le_mul hqf hqf (by linarith) (by linarith)]
  have hr3' : (27 : ℝ) ≤ r ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hr3 3
    norm_num at this
    linarith
  have hf2' : (4 : ℝ) ≤ (f : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hf2 2
    norm_num at this
    linarith
  have h30 : (30 : ℝ) ≤ r ^ 3 * (f : ℝ) ^ 2 := by
    have := mul_le_mul hr3' hf2' (by norm_num) (by linarith)
    linarith
  have hL4 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL
  have hr0 : 0 ≤ r := by linarith
  have hrf : 0 ≤ r * (f : ℝ) ^ 2 := mul_nonneg hr0 (by positivity)
  calc 120 * r * q ^ ((3 : ℝ) / 2) ≤ 120 * r * q ^ 2 := mul_le_mul_of_nonneg_left hpow (by linarith)
    _ ≤ 120 * r * ((f : ℝ) ^ 2 / 4) := mul_le_mul_of_nonneg_left hq2 (by linarith)
    _ = (r * (f : ℝ) ^ 2) * 30 := by ring
    _ ≤ (r * (f : ℝ) ^ 2) * (r ^ 3 * (f : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h30 hrf
    _ = (r * f) ^ 4 * 1 := by ring
    _ ≤ (r * f) ^ 4 * L ^ 4 := mul_le_mul_of_nonneg_left hL4 (by positivity)
    _ = (r * f * L) ^ 4 := by ring
end Formalism.HermitianLattices.GenusMassVolumes
