-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.thrW_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:41:09.87404+00:00
-- url     : https://prove2.me/submissions/b6c63e87-c3fd-4f7e-b8f2-ad090f9d1ba0

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalMeasurabilityWeakThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNormalization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
theorem _root_.solution (k r o : ℕ) (A : ℝ)
    (h : 12 * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A o := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ho : (0 : ℝ) ≤ o := Nat.cast_nonneg o
  push_cast at h
  constructor <;>
    nlinarith [mul_nonneg (mul_nonneg hr hr) (mul_nonneg hr hr), mul_nonneg (mul_nonneg hr hr) (mul_nonneg hr hk),
      mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg hr hr, mul_nonneg (mul_nonneg hr hr) hk, mul_nonneg hr hk,
      mul_nonneg (mul_nonneg hr hr) ho, mul_nonneg hr ho]
end Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
