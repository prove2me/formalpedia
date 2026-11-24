-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HaarScaling.AB_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:07.76502+00:00
-- url     : https://prove2.me/submissions/ddb3a245-a51b-42eb-b749-15a7a5c46260

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.HaarScaling
theorem _root_.solution (k r : ℕ) (A : ℝ) (h : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A) : AB k r ≤ A := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  unfold AB
  push_cast at h
  nlinarith [mul_nonneg hk hr, mul_nonneg hk hk, mul_nonneg hr hr]
end Formalism.FourierDecayAlt.P.HaarScaling
