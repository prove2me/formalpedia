-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.dj_conjM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:07:14.891819+00:00
-- url     : https://prove2.me/submissions/75b06f4a-f3ee-456f-85ef-357e3731c057

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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  unfold conjM
  exact ((continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const
end Formalism.FourierDecayAlt.P.B2x8
