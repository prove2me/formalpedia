-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.conjM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:13:56.8128+00:00
-- url     : https://prove2.me/submissions/4cb80c9a-4387-48a6-847a-e8605c1a3a5c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  unfold conjM
  exact ((continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const
end Formalism.FourierDecayAlt.P.B2x1
