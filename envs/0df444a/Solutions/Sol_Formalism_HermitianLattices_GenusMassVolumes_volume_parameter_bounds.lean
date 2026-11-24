-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.volume_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:44.40491+00:00
-- url     : https://prove2.me/submissions/0df0ee15-ffa3-4f3e-adbf-53578c463e6c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FactorialProductRearrangement

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
theorem _root_.solution : VolumeParameterBounds := by
  intro e q d he hq hd
  dsimp only
  have he' : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hd' : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hpe : (2 : ℝ) ^ (-(e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hpe0 : 0 < (2 : ℝ) ^ (-(e : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hx : (2 : ℝ) ≤ (e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ)) := by linarith
  have h4x : (4 : ℝ) ≤ (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) := by
    have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by rw [Real.rpow_two]; norm_num
    rw [← h22]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
  have hqd : (21 : ℝ) ≤ q * d := by nlinarith
  have hs : (4 : ℝ) ≤ Real.sqrt (q * d) := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h16]
    exact Real.sqrt_le_sqrt (by linarith)
  constructor
  · have hprod : (16 : ℝ) ≤ (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt (q * d) := by
      nlinarith
    linarith [Real.pi_le_four]
  · have hs0 : 0 < Real.sqrt (q * d) := by linarith
    have h2x0 : 0 < (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) := by positivity
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul h2x0.ne' hs0.ne',
      Real.log_rpow (by norm_num), Real.log_sqrt (by positivity),
      Real.log_mul (two_ne_zero : (2 : ℝ) ≠ 0) (pow_ne_zero e (two_ne_zero : (2 : ℝ) ≠ 0)),
      Real.log_pow]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [mul_pos hpe0 hl2]
end Formalism.HermitianLattices.GenusMassVolumes
