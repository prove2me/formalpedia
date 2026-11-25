-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.continuous_fsv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:34:41.135973+00:00
-- url     : https://prove2.me/submissions/765dfd6e-cd85-4b93-9cc6-7460639c3a82

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqOfContinuousOffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (s : ℂ) : Continuous (fsv s) := by
  unfold fsv
  exact ((continuous_const.mul continuous_id).sub
    (continuous_const.mul Complex.continuous_conj)).cexp
end Formalism.FourierDecayAlt.P5
