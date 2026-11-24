-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.lift_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:00:47.057169+00:00
-- url     : https://prove2.me/submissions/b09cf5f7-5ecd-4749-b935-074f9377286c

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
theorem _root_.solution (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y = mk3 k r' 0 y 0 := by
  funext i
  have hi := i.isLt
  rw [three_block_apply]
  simp only [liftVec]
  split_ifs <;> first | omega | simp
end Formalism.FourierDecayAlt.P.B2x8
