-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.rmulF_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:52.354784+00:00
-- url     : https://prove2.me/submissions/8b41b565-3b43-46e7-bd7a-07bf844aba7d

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
theorem _root_.solution {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulF a) := by
  unfold rmulF
  exact (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).matrix_mul continuous_const
end Formalism.FourierDecayAlt.P.B2x1
