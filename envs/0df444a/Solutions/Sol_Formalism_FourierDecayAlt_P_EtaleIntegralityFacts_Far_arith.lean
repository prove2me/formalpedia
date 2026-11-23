-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far.arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:48.448653+00:00
-- url     : https://prove2.me/submissions/73e8eff8-030d-41e7-8bb7-985711d4a25e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
theorem _root_.solution (a b q j m : ℕ) (hj : j ≤ q) (cW τ : ℝ) (hcW : 1 ≤ cW) (hτ : 1 ≤ τ) :
    (cW * τ ^ (4 * (m + 2))) ^ a * ((cW * τ ^ (4 * (m + 2))) ^ b) ^ j ≤
      cW ^ (a + b * q) * τ ^ (4 * (a + b) * (m + 2) * (j + 1)) := by
  have e : (cW * τ ^ (4 * (m + 2))) ^ a * ((cW * τ ^ (4 * (m + 2))) ^ b) ^ j =
      cW ^ (a + b * j) * τ ^ (4 * (m + 2) * (a + b * j)) := by
    rw [← pow_mul, ← pow_add, mul_pow, ← pow_mul]
  rw [e]
  have h1 : a + b * j ≤ a + b * q := Nat.add_le_add_left (Nat.mul_le_mul_left b hj) a
  have h2 : 4 * (m + 2) * (a + b * j) ≤ 4 * (a + b) * (m + 2) * (j + 1) := by
    calc 4 * (m + 2) * (a + b * j) ≤ 4 * (m + 2) * ((a + b) * (j + 1)) :=
          Nat.mul_le_mul_left _ (by nlinarith [Nat.zero_le (a * j), Nat.zero_le b])
      _ = 4 * (a + b) * (m + 2) * (j + 1) := by ring
  exact mul_le_mul (pow_le_pow_right₀ hcW h1) (pow_le_pow_right₀ hτ h2) (by positivity) (by positivity)
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
