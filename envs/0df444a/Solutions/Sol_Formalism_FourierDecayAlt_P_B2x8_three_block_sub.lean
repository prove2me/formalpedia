-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.three_block_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:56.478364+00:00
-- url     : https://prove2.me/submissions/0d043607-0eeb-454f-ba3d-2e93365a8cd1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (a a' b b' : ℂ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    mk3 k r' a y b - mk3 k r' a' y' b' = mk3 k r' (a - a') (y - y') (b - b') := by
  funext i
  simp only [Pi.sub_apply, three_block_apply]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.B2x8
