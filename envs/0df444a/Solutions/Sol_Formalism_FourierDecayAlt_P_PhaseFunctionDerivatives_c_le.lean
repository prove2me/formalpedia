-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.c_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:19.342059+00:00
-- url     : https://prove2.me/submissions/b8feb3d6-d142-485e-abad-5419dfb74b1c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution (a : ℝ) (ha : 0 ≤ a) (E' : ℕ) (d A : ℝ) (hd : 0 ≤ d) (hA : (E' : ℝ) + d + 1 ≤ A) :
    (1 + a) ^ E' * (max 1 a) ^ (-A) ≤ 2 ^ ((E' : ℝ) + d + 1) * (1 + a) ^ (-(d + 1)) := by
  have hM1 : (1 : ℝ) ≤ max 1 a := le_max_left _ _
  have h1a : (0 : ℝ) < 1 + a := by linarith
  have hM2 : (1 + a) / 2 ≤ max 1 a := by
    rcases le_total a 1 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (E' : ℝ) + d + 1 := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  rw [← hp] at hA ⊢
  have s1 : (max 1 a) ^ (-A) ≤ (max 1 a) ^ (-p) := Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have s2 : (max 1 a) ^ (-p) ≤ ((1 + a) / 2) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hM2 (by linarith)
  have s3 : ((1 + a) / 2) ^ (-p) = 2 ^ p * (1 + a) ^ (-p) := by
    rw [Real.div_rpow h1a.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  have s4 : (1 + a) ^ E' * (1 + a) ^ (-p) = (1 + a) ^ (-(d + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add h1a]; congr 1; rw [hp]; ring
  calc (1 + a) ^ E' * (max 1 a) ^ (-A) ≤ (1 + a) ^ E' * (2 ^ p * (1 + a) ^ (-p)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← s3]; exact s1.trans s2
    _ = 2 ^ p * ((1 + a) ^ E' * (1 + a) ^ (-p)) := by ring
    _ = _ := by rw [s4]
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
