-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.inLie_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:27:50.061024+00:00
-- url     : https://prove2.me/submissions/c8c6e0b4-7403-42bf-9f70-6a2b12153991

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {X : Mat k r} (hX : inLie k r X) (c : ℝ) : inLie k r ((c : ℂ) • X) := by
  unfold inLie at *
  have hc : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
  rw [Matrix.conjTranspose_smul, hc, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]
end Formalism.FourierDecayAlt.P.B4
