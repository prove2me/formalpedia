-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholds_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:41.10039+00:00
-- url     : https://prove2.me/submissions/4732a408-3222-4397-aef4-e835c415310e

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
theorem _root_.solution : ScaleThresholds := by
  intro ka ell sb TT i s r hka hell hTT hi
  have e : ∀ m : ℕ, (4 * ka / ell) ^ m = (4 / ell) ^ m * ka ^ m := fun m => by rw [← mul_pow]; ring
  have key1 : ka ^ ((2 * i : ℤ) - 3) * ka = ka ^ (2 * i - 2) := by
    rw [← zpow_add_one₀ hka.ne', ← zpow_natCast]; congr 1; omega
  have key2 : ka ^ ((2 * i + s : ℤ) - 3) * ka = ka ^ (2 * (i - 1) + s) := by
    rw [← zpow_add_one₀ hka.ne', ← zpow_natCast]; congr 1; omega
  have k3 : (ka ^ (4 * r)) ^ (-(1 / 2 : ℝ)) = (ka ^ (2 * r))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, show 4 * r = 2 * r * 2 by ring, pow_mul,
      Real.sqrt_sq (by positivity)]
  have key3 : ka ^ (2 * (i + r - 1)) * ka = ka ^ (2 * i - 1) * ka ^ (2 * r) := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have hk2 : ka ^ (2 * r) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    linear_combination (Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ (2 * i - 2) * sb) * key1
  · rw [e]
    linear_combination (Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ (2 * (i - 1) + s) * sb) * key2
  · rw [Real.mul_rpow (by positivity) hTT.le, k3]
    have hinv := mul_inv_cancel₀ hk2
    linear_combination (Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * (i - 1)) * sb *
      TT ^ (-(1 / 2 : ℝ)) * (ka ^ (2 * r))⁻¹) * key3 +
      (Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * (i - 1)) * sb * TT ^ (-(1 / 2 : ℝ)) *
        ka ^ (2 * i - 1)) * hinv
end Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
