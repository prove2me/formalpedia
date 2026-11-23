-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsBelow_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:40.972745+00:00
-- url     : https://prove2.me/submissions/c9b703f9-a5c9-4d78-a634-a74353d11859

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScaleThresholdCharacters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
theorem _root_.solution : ScaleThresholdsBelow := by
  intro ka ell sb TT N IL m i hka hell hN hIL hsb hTT hle
  have h4 : 4 / ell ≤ 28 * N / IL := by
    rw [div_le_div_iff₀ hell hIL]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 7 * N)).mp hle
    nlinarith
  have hE1 : Real.exp (1 / 4) / 2 ≤ 1 := by
    have h4e : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have hlt := Real.exp_one_lt_d9
    have hpos := Real.exp_pos (1 / 4)
    by_contra hc
    have hc' : 2 < Real.exp (1 / 4) := by linarith [not_le.mp hc]
    have h16 : (2:ℝ) ^ 4 < Real.exp (1 / 4) ^ 4 := pow_lt_pow_left₀ hc' (by norm_num) (by norm_num)
    norm_num at h16
    linarith
  have hE2 : Real.exp (3 / 2) / 4 ≤ 2 := by
    have h2e : Real.exp (3 / 2) ^ 2 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have hlt := Real.exp_one_lt_d9
    have hpos := Real.exp_pos 1
    have hpos' := Real.exp_pos (3 / 2)
    by_contra hc
    have hc' : 8 < Real.exp (3 / 2) := by linarith [not_le.mp hc]
    have h64 : (8:ℝ) ^ 2 < Real.exp (3 / 2) ^ 2 := pow_lt_pow_left₀ hc' (by norm_num) (by norm_num)
    have h3 : Real.exp 1 ^ 3 < 3 ^ 3 := pow_lt_pow_left₀ (by linarith) hpos.le (by norm_num)
    rw [h2e] at h64
    norm_num at h64 h3
    linarith
  refine ⟨?_, ?_⟩
  · have hX : (4 * ka / ell) ^ m ≤ (28 * ka * N / IL) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      rw [show 4 * ka / ell = ka * (4 / ell) by ring, show 28 * ka * N / IL = ka * (28 * N / IL) by ring]
      exact mul_le_mul_of_nonneg_left h4 hka.le
    calc Real.exp (1 / 4) / 2 * sb * (4 * ka / ell) ^ m ≤ Real.exp (1 / 4) / 2 * sb * (28 * ka * N / IL) ^ m :=
          mul_le_mul_of_nonneg_left hX (mul_nonneg (by positivity) hsb)
      _ ≤ 1 * sb * (28 * ka * N / IL) ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE1 hsb) (by positivity)
      _ = sb * (28 * ka * N / IL) ^ m := by ring
  · have hA : (4 / ell) ^ (2 * (i - 1)) ≤ (28 * N / IL) ^ (2 * (i - 1)) :=
      pow_le_pow_left₀ (by positivity) h4 _
    have hC : 0 ≤ sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg hsb (by positivity)) (Real.rpow_nonneg hTT.le _)
    calc Real.exp (3 / 2) / 4 * sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) * (4 / ell) ^ (2 * (i - 1))
        = (Real.exp (3 / 2) / 4) * (sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ))) *
            (4 / ell) ^ (2 * (i - 1)) := by ring
      _ ≤ 2 * (sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ))) * (28 * N / IL) ^ (2 * (i - 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hE2 hC) hA (by positivity) (mul_nonneg (by norm_num) hC)
      _ = 2 * sb * ka ^ (2 * i - 1) * TT ^ (-(1 / 2 : ℝ)) * (28 * N / IL) ^ (2 * (i - 1)) := by ring
end Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
